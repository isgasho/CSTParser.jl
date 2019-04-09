module CSTParser
global debug = true

using Tokenize
import Base: length, first, last, getindex, setindex!
import Tokenize.Tokens
import Tokenize.Tokens: RawToken, AbstractToken, iskeyword, isliteral, isoperator, untokenize
import Tokenize.Lexers: Lexer, peekchar, iswhitespace

export ParseState, parse_expression

include("lexer.jl")
include("spec.jl")
include("utils.jl")
include("recovery.jl")
include("components/internals.jl")
include("components/keywords.jl")
include("components/lists.jl")
include("components/operators.jl")
include("components/strings.jl")
include("conversion.jl")
include("display.jl")
include("interface.jl")


"""
    parse_expression(ps)

Parses an expression until `closer(ps) == true`. Expects to enter the
`ParseState` the token before the the beginning of the expression and ends
on the last token.

Acceptable starting tokens are:
+ A keyword
+ An opening parentheses or brace.
+ An operator.
+ An instance (e.g. identifier, number, etc.)
+ An `@`.

"""
@addctx :expr function parse_expression(ps::ParseState)
    if ps.nt.kind == Tokens.COMMA
        push!(ps.errors, Error((ps.nt.startbyte:ps.nws.endbyte) .+ 1, "Expression began with a comma."))
        ret = ErrorToken(PUNCTUATION(next(ps)))
    elseif ps.nt.kind ∈ term_c && ps.nt.kind != Tokens.END
        push!(ps.errors, Error((ps.nt.startbyte:ps.nws.endbyte) .+ 1, "Expression began with a terminal token: $(ps.nt.kind)."))
        ret = ErrorToken(INSTANCE(next(ps)))
    else
        next(ps)
        if iskeyword(ps.t.kind) && ps.t.kind != Tokens.DO
            ret = parse_kw(ps)
        elseif ps.t.kind == Tokens.LPAREN
            ret = parse_paren(ps)
        elseif ps.t.kind == Tokens.LSQUARE
            ret = @default ps parse_array(ps)
        elseif ps.t.kind == Tokens.LBRACE
            ret = @default ps @closebrace ps parse_braces(ps)
        elseif isinstance(ps.t) || isoperator(ps.t)
            if ps.t.kind == Tokens.WHERE
                ret = IDENTIFIER(ps)
            else
                ret = INSTANCE(ps)
            end
            if is_colon(ret) && ps.nt.kind != Tokens.COMMA
                ret = parse_unary(ps, ret)
            end
        elseif ps.t.kind == Tokens.AT_SIGN
            ret = parse_macrocall(ps)
        else
            ret = ErrorToken(INSTANCE(ps))
            push!(ps.errors, Error((ps.nt.startbyte:ps.nws.endbyte) .+ 1, "Expression began with a : $(ps.nt.kind)."))
        end

        while !closer(ps)
            ret = parse_compound(ps, ret)
        end
    end
    return ret
end

function parse_compound(ps::ParseState, @nospecialize ret)
    if ps.nt.kind == Tokens.FOR
        ret = parse_generator(ps, ret)
    elseif ps.nt.kind == Tokens.DO
        ret = @default ps @closer ps block parse_do(ps, ret)
    elseif isajuxtaposition(ps, ret)
        op = OPERATOR(0, 0, Tokens.STAR, false)
        ret = parse_operator(ps, ret, op)
    elseif (ret isa EXPR{x_Str} ||  ret isa EXPR{x_Cmd}) && ps.nt.kind == Tokens.IDENTIFIER
        arg = IDENTIFIER(next(ps))
        push!(ret, LITERAL(arg.fullspan, arg.span, val(ps.t, ps), Tokens.STRING))
    elseif (ret isa IDENTIFIER || (ret isa BinarySyntaxOpCall && is_dot(ret.op))) && (ps.nt.kind == Tokens.STRING || ps.nt.kind == Tokens.TRIPLE_STRING || ps.nt.kind == Tokens.CMD)
        next(ps)
        arg = parse_string_or_cmd(ps, ret)
        head = arg.kind == Tokens.CMD ? x_Cmd : x_Str
        ret = EXPR{head}(Any[ret, arg])
    elseif ps.nt.kind == Tokens.LPAREN
        no_ws = !isemptyws(ps.ws)
        err_rng = ps.t.endbyte + 2:ps.nt.startbyte 
        ret = @closeparen ps parse_call(ps, ret)
        if no_ws && !(ret isa UnaryOpCall || ret isa UnarySyntaxOpCall)
            push!(ps.errors, Error(err_rng, "White space in function call."))
            ret = ErrorToken(ret)
        end
    elseif ps.nt.kind == Tokens.LBRACE
        if isemptyws(ps.ws)
            ret = @default ps @nocloser ps inwhere @closebrace ps parse_curly(ps, ret)
        else
            push!(ps.errors, Error(ps.t.endbyte + 2:ps.nt.startbyte , "White space in brace call."))
            ret = ErrorToken(@default ps @nocloser ps inwhere @closebrace ps parse_curly(ps, ret))
        end
    elseif ps.nt.kind == Tokens.LSQUARE && isemptyws(ps.ws) && !(ret isa OPERATOR)
        ret = @default ps @nocloser ps block parse_ref(ps, ret)
    elseif ps.nt.kind == Tokens.COMMA
        ret = parse_tuple(ps, ret)
    elseif isunaryop(ret) && ps.nt.kind != Tokens.EQ
        ret = parse_unary(ps, ret)
    elseif isoperator(ps.nt)
        op = OPERATOR(next(ps))
        ret = parse_operator(ps, ret, op)
    elseif ret isa UnarySyntaxOpCall && is_prime(ret.arg2)
        # prime operator followed by an identifier has an implicit multiplication
        nextarg = @precedence ps 11 parse_expression(ps)
        ret = BinaryOpCall(ret, OPERATOR(0, 0, Tokens.STAR,false), nextarg)
################################################################################
# Everything below here is an error
################################################################################
    elseif ps.nt.kind in (Tokens.RPAREN, Tokens.RSQUARE, Tokens.RBRACE)
        push!(ps.errors, Error((ps.t.startbyte:ps.nt.endbyte) .+ 1 , "Disallowed compound expression."))
        ret = EXPR{ErrorToken}([ret, ErrorToken(PUNCTUATION(next(ps)))])
    else
        push!(ps.errors, Error((ps.t.startbyte:ps.nt.endbyte) .+ 1 , "Disallowed compound expression."))
        nextarg = parse_expression(ps)
        ret = EXPR{ErrorToken}([ret, nextarg])
    end
    return ret
end

"""
    parse_paren(ps, ret)

Parses an expression starting with a `(`.
"""
@addctx :paren function parse_paren(ps::ParseState)  
    args = Any[PUNCTUATION(ps)]
    @closeparen ps @default ps @nocloser ps inwhere parse_comma_sep(ps, args, false, true, true)

    if length(args) == 2 && ((ps.ws.kind != SemiColonWS || (length(args) == 2 && args[2] isa EXPR{Block})) && !(args[2] isa EXPR{Parameters}))
        accept_rparen(ps, args)
        ret = EXPR{InvisBrackets}(args)
    else
        accept_rparen(ps, args)
        ret = EXPR{TupleH}(args)
    end
    return ret
end

"""
    parse(str, cont = false)

Parses the passed string. If `cont` is true then will continue parsing until the end of the string returning the resulting expressions in a TOPLEVEL block.
"""
function parse(str::String, cont = false)
    ps = ParseState(str)
    x, ps = parse(ps, cont)
    return x
end

function parse_doc(ps::ParseState)
    if (ps.nt.kind == Tokens.STRING || ps.nt.kind == Tokens.TRIPLE_STRING) && !isemptyws(ps.nws)
        doc = LITERAL(next(ps))
        if (ps.nt.kind == Tokens.ENDMARKER || ps.nt.kind == Tokens.END)
            return doc
        elseif isbinaryop(ps.nt) && !closer(ps)
            ret = parse_compound(ps, doc)
            return ret
        end

        ret = parse_expression(ps)
        ret = EXPR{MacroCall}(Any[GlobalRefDOC(), doc, ret])
    elseif ps.nt.kind == Tokens.IDENTIFIER && val(ps.nt, ps) == "doc" && (ps.nnt.kind == Tokens.STRING || ps.nnt.kind == Tokens.TRIPLE_STRING)
        doc = IDENTIFIER(next(ps))
        next(ps)
        arg = parse_string_or_cmd(ps, doc)
        doc = EXPR{x_Str}(Any[doc, arg])
        ret = parse_expression(ps)
        ret = EXPR{MacroCall}(Any[GlobalRefDOC(), doc, ret])
    else
        ret = parse_expression(ps)
    end
    return ret
end

function parse(ps::ParseState, cont = false)
    if ps.l.io.size == 0
        return (cont ? EXPR{FileH}(Any[]) : nothing), ps
    end
    last_line = 0
    curr_line = 0

    if cont
        top = EXPR{FileH}(Any[])
        if ps.nt.kind == Tokens.WHITESPACE || ps.nt.kind == Tokens.COMMENT
            next(ps)
            push!(top, LITERAL(ps.nt.startbyte, ps.nt.startbyte, "", Tokens.NOTHING, Meta(top, nothing, nothing, nothing, nothing)))
        end

        while !ps.done && !ps.errored
            curr_line = ps.nt.startpos[1]
            ret = parse_doc(ps)

            # join semicolon sep items
            if curr_line == last_line && last(top.args) isa EXPR{TopLevel}
                push!(last(top.args), setparent!(ret, last(top.args)))
            elseif ps.ws.kind == SemiColonWS
                push!(top, EXPR{TopLevel}(Any[ret]))
            else
                push!(top, ret)
            end
            last_line = curr_line
        end
    else
        if ps.nt.kind == Tokens.WHITESPACE || ps.nt.kind == Tokens.COMMENT
            next(ps)
            top = LITERAL(ps.nt.startbyte, ps.nt.startbyte, "", Tokens.NOTHING)
        else
            top = parse_doc(ps)
            last_line = ps.nt.startpos[1]
            if ps.ws.kind == SemiColonWS
                top = EXPR{TopLevel}(Any[top])
                while ps.ws.kind == SemiColonWS && ps.nt.startpos[1] == last_line && ps.nt.kind != Tokens.ENDMARKER
                    ret = parse_doc(ps)
                    push!(top, ret)
                    last_line = ps.nt.startpos[1]
                end
            end
        end
    end

    return top, ps
end


function parse_file(path::String)
    x = parse(read(path, String), true)
    File([], [], path, x, [])
end

function parse_directory(path::String, proj = Project(path, []))
    for f in readdir(path)
        if isfile(joinpath(path, f)) && endswith(f, ".jl")
            try
                push!(proj.files, parse_file(joinpath(path, f)))
            catch
                println("$f failed to parse")
            end
        elseif isdir(joinpath(path, f))
            parse_directory(joinpath(path, f), proj)
        end
    end
    proj
end

"""
Provides for incremental updating of CST.
"""
module Reparser
using CSTParser
import CSTParser: parse

# expression types
import CSTParser: AbstractEXPR, IDENTIFIER, LITERAL, PUNCTUATION, KEYWORD, OPERATOR, EXPR
import CSTParser: UnaryOpCall, UnarySyntaxOpCall, BinaryOpCall, BinarySyntaxOpCall, WhereOpCall, ConditionalOpCall, FileH, Block, If
const EXPRStack = Tuple{AbstractEXPR,Int,Int}

Base.getindex(x::UnaryOpCall, i) = i == 1 ? x.op : 
                                            x.arg
Base.getindex(x::UnarySyntaxOpCall, i) = i == 1 ? x.arg1 : 
                                                  x.arg2
Base.getindex(x::BinaryOpCall, i) = i == 1 ? x.arg1 : 
                                    i == 2 ? x.op : 
                                             x.arg2
Base.getindex(x::BinarySyntaxOpCall, i) = i == 1 ? x.arg1 : 
                                          i == 2 ? x.op : 
                                                   x.arg2
Base.getindex(x::WhereOpCall, i) = i == 1 ? x.arg1 : 
                                   i == 2 ? x.op : 
                                            x.args[i - 2]
Base.getindex(x::ConditionalOpCall, i) = i == 1 ? x.cond : 
                                         i == 2 ? x.op1 : 
                                         i == 3 ? x.arg1 : 
                                         i == 4 ? x.op2 : 
                                                  x.arg2
Base.getindex(x::EXPR, i) = x.args[i]

Base.setindex!(x::UnaryOpCall, a, i) = i == 1 ? (x.op = a) : 
                                                (x.arg = a)
Base.setindex!(x::UnarySyntaxOpCall, a, i) = i == 1 ? (x.arg1 = a) : 
                                                      (x.arg2 = a)
Base.setindex!(x::BinaryOpCall, a, i) = i == 1 ? (x.arg1 = a) : 
                                        i == 2 ? (x.op = a) : 
                                                 (x.arg2 = a)
Base.setindex!(x::BinarySyntaxOpCall, a, i) = i == 1 ? (x.arg1 = a) : 
                                              i == 2 ? (x.op = a) : 
                                                       (x.arg2 = a)
Base.setindex!(x::WhereOpCall, a, i) = i == 1 ? (x.arg1 = a) : 
                                       i == 2 ? (x.op = a) : 
                                                (x.args[i - 2] = a)
Base.setindex!(x::ConditionalOpCall, a, i) = i == 1 ? (x.cond = a) : 
                                             i == 2 ? (x.op1 = a) : 
                                             i == 3 ? (x.arg1 = a) : 
                                             i == 4 ? (x.op2 = a) : 
                                                      (x.arg2 = a)
Base.setindex!(x::EXPR, a, i) = (x.args[i] = a)

function find_enclosing_expr(cst, offset, pos = 0, stack = EXPRStack[])
    pos1 = pos
    for (i,a) in enumerate(cst)
        if pos < first(offset) < pos + a.span && pos < last(offset) < pos + a.span
            push!(stack, (cst, pos1, i))
            return find_enclosing_expr(a, offset, pos, stack)
        else 
            pos += a.fullspan
        end
    end
    push!(stack, (cst, pos1, 0))
    return stack
end

containing_expr(stack) = first(last(stack))
parent_expr(stack) = first(stack[end-1])
insert_size(inserttext, insertrange) = sizeof(inserttext) - max(last(insertrange) - first(insertrange), 0)
enclosing_expr_range(stack, insertsize) = last(stack)[2] .+ (1:first(last(stack)).fullspan + insertsize)

function reparse(edittedtext::String, inserttext::String, insertrange::UnitRange{Int}, oldcst)
    #need to handle empty replacement case, i.e. inserttext = ""
    stack = find_enclosing_expr(oldcst, insertrange)
    insertsize = insert_size(inserttext, insertrange)
    reparsed = reparse(stack, edittedtext, insertsize, oldcst)
    return reparsed, oldcst
end


function replace_args!(replacement_args, stack)
    pexpr, ppos, pi = stack[end-1]
    oldspan, oldfullspan = pexpr.args[pi].span, pexpr.args[pi].fullspan
    if length(replacement_args) > 1
        deleteat!(pexpr.args, pi)
        for i = 0:length(replacement_args)-1
            insert!(pexpr.args, pi + i, replacement_args[1 + i])
        end
    else
        pexpr.args[pi] = replacement_args[1]
        dfullspan = replacement_args[1].fullspan - oldfullspan
        @info "Replacing $(typeof(pexpr)) at $(pi)"
        fix_stack_span(stack, dfullspan, replacement_args[1].span - replacement_args[1].fullspan)
    end 
end

function reparse(stack::Array{EXPRStack}, edittedtext::String, insertsize::Int, oldcst)
    # Assume no existing error in CST
    # need to update (full)spans
    if length(stack) == 1
        return false
    else
        if parent_expr(stack) isa EXPR{FileH} 
            replacement_args = parse(edittedtext[enclosing_expr_range(stack, insertsize)], true).args
        elseif parent_expr(stack) isa EXPR{Block} && !(length(stack) > 2 && stack[end-2] isa EXPR{If})
            replacement_args = let 
                ps = ParseState(edittedtext[enclosing_expr_range(stack, insertsize)])
                newblockargs = Any[]
                CSTParser.parse_block(ps, newblockargs)
            end
        else
            pop!(stack)
            return reparse(stack, edittedtext, insertsize, oldcst)
        end
        replace_args!(replacement_args, stack)
        return true
    end
    return false
end

function fixlastchild(x, pi, dspan)
    nx = length(x)
    if pi == nx
        x[pi] = x.fullspan - dspan
        return true
    elseif x[nx].fullspan == 0 
        for i = nx-1:-1:1
            if x[i].fullspan > 0
                x[pi] = x.fullspan - dspan
                return true
            end
        end
    end
    return false
end

function fix_stack_span(stack::Array{EXPRStack}, dfullspan, dspan)
    islast = true
    for i = length(stack)-1:-1:1
        stack[i][1].fullspan += dfullspan
        if islast && stack[i][3] == length(stack[i][1])
            stack[i][1].span = stack[i][1].fullspan + dspan
        else
            stack[i][1].span += dfullspan
            islast = false
        end
    end
end

function test(text, insertrange, inserttext)
    cst = parse(text, true) 
    cst0 = deepcopy(cst)
    edittedtext = edit_string(text, insertrange, inserttext)
    reparsed, reparsed_cst = reparse(edittedtext, inserttext, insertrange, cst)
    new_cst = CSTParser.parse(edittedtext, true)
    return reparsed, isequiv(new_cst, reparsed_cst), text, edittedtext, cst0, new_cst, reparsed_cst
end

function edit_string(text, insertrange, inserttext)
    if first(insertrange) == last(insertrange) == 0
        text = string(inserttext, text)
    elseif first(insertrange) == 0 && last(insertrange) == sizeof(text)
        text = inserttext
    elseif first(insertrange) == 0
        text = string(inserttext, text[nextind(text, last(insertrange)):end])
    elseif first(insertrange) == last(insertrange) == sizeof(text)
        text = string(text, inserttext)
    elseif last(insertrange) == sizeof(text)
        text = string(text[1:first(insertrange)], inserttext)
    else
        text = string(text[1:first(insertrange)], inserttext, text[nextind(text, last(insertrange)):end])
    end    
end

spanequiv(a,b) = a.span == b.span && a.fullspan == b.fullspan
 
isequiv(a,b; span = true) = false
isequiv(a::IDENTIFIER, b::IDENTIFIER; span = true) = a.val == b.val && (!span || spanequiv(a,b))
isequiv(a::LITERAL, b::LITERAL; span = true) = a.val == b.val && a.kind == b.kind  && (!span || spanequiv(a,b))
isequiv(a::KEYWORD, b::KEYWORD; span = true) = a.kind == b.kind  && (!span || spanequiv(a,b))
isequiv(a::OPERATOR, b::OPERATOR; span = true) = a.kind == b.kind && a.dot == b.dot  && (!span || spanequiv(a,b))
isequiv(a::PUNCTUATION, b::PUNCTUATION; span = true) = a.kind == b.kind  && (!span || spanequiv(a,b))
isequiv(a::UnaryOpCall, b::UnaryOpCall; span = true) = isequiv(a.op, b.op, span = span) && isequiv(a.arg, b.arg, span = span) && (!span || spanequiv(a,b))
isequiv(a::UnarySyntaxOpCall, b::UnarySyntaxOpCall; span = true) = isequiv(a.arg1, b.arg1, span = span) && isequiv(a.arg2, b.arg2, span = span) && (!span || spanequiv(a,b))
isequiv(a::T, b::T; span = true) where T <: Union{BinaryOpCall,BinarySyntaxOpCall} = isequiv(a.arg1, b.arg1, span = span) && isequiv(a.op, b.op, span = span) && isequiv(a.arg2, b.arg2, span = span) && (!span || spanequiv(a,b))

function isequiv(a::WhereOpCall,b::WhereOpCall;span = true)
    t = isequiv(a.arg1, b.arg1, span = span) &&
    isequiv(a.op, b.op, span = span)
    length(a.args) != length(b.args) && return false
    for i = 1:length(a.args)
        t = t && isequiv(a.args[i], b.args[i], span = span) 
        t || return false
    end
    return t && (!span || spanequiv(a,b))
end

function isequiv(a::ConditionalOpCall,b::ConditionalOpCall; span = true)
    isequiv(a.cond, b.cond, span = span) && 
    isequiv(a.arg1, b.arg1, span = span) && 
    isequiv(a.op1, b.op1, span = span) &&
    isequiv(a.arg2, b.arg2, span = span) && 
    isequiv(a.op2, b.op2, span = span) && (!span || spanequiv(a,b))
end

function isequiv(a::EXPR{S},b::EXPR{T}; span = true) where {S,T}
    t = S == T
    length(a.args) != length(b.args) && return false
    for i = 1:length(a.args)
        t = t && isequiv(a.args[i], b.args[i], span = span) 
        t || return false
    end
    return t && (!span || spanequiv(a,b))
end

end
using .Reparser
fff() = ()
end
