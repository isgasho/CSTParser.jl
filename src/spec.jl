# Operator hierarchy
const AssignmentOp  = 1
const ConditionalOp = 2
const ArrowOp       = 3
const LazyOrOp      = 4
const LazyAndOp     = 5
const ComparisonOp  = 6
const PipeOp        = 7
const ColonOp       = 8
const PlusOp        = 9
const BitShiftOp    = 10
const TimesOp       = 11
const RationalOp    = 12
const PowerOp       = 13
const DeclarationOp = 14
const WhereOp       = 15
const DotOp         = 16
const PrimeOp       = 16
const DddotOp       = 7
const AnonFuncOp    = 14

abstract type AbstractEXPR end
abstract type LeafNode <: AbstractEXPR end

mutable struct Binding
    name::String
    refs::Vector{Any}
    val
end    
Binding(name) = Binding(name, AbstractEXPR[], nothing)

mutable struct Meta
    parent#::Union{Nothing,AbstractEXPR}
    binding#::Union{Nothing,Binding}
    ref
    scope::Union{Nothing,Dict}
    store::Any
end
Meta(;parent = nothing, binding = nothing, ref = nothing, scope = nothing) = Meta(parent, binding, ref, scope, nothing)

mutable struct EXPR{T} <: AbstractEXPR
    args::Vector
    fullspan::Int
    span::Int
    meta::Meta
end
function EXPR{T}(args, fullspan, span) where T
    ret = EXPR{T}(args, fullspan, span, Meta())
    for i = 1:length(args)
        setparent!(ret.args[i], ret)
    end
    return ret
end
function EXPR{T}(args::Vector) where {T}
    ret = EXPR{T}(args, 0, 0)
    update_span!(ret)
    ret
end
    
struct IDENTIFIER <: LeafNode
    fullspan::Int
    span::Int
    val::String
    meta::Meta
    IDENTIFIER(fullspan::Int, span::Int, val::String, meta::Meta) = new(fullspan, span, val, meta)
end
IDENTIFIER(fullspan::Int, span::Int, val::String) = IDENTIFIER(fullspan, span, val, Meta())
@noinline IDENTIFIER(ps::ParseState) = IDENTIFIER(ps.nt.startbyte - ps.t.startbyte, ps.t.endbyte - ps.t.startbyte + 1, val(ps.t, ps))

struct PUNCTUATION <: LeafNode
    kind::Tokenize.Tokens.Kind
    fullspan::Int
    span::Int
    meta::Meta
    PUNCTUATION(kind::Tokenize.Tokens.Kind, fullspan::Int, span::Int, meta::Meta) = new(kind, fullspan, span, meta)
end
@noinline PUNCTUATION(kind::Tokenize.Tokens.Kind, fullspan::Int, span::Int) = PUNCTUATION(kind, fullspan, span, Meta())
@noinline PUNCTUATION(ps::ParseState) = PUNCTUATION(ps.t.kind, ps.nt.startbyte - ps.t.startbyte, ps.t.endbyte - ps.t.startbyte + 1)

struct OPERATOR <: LeafNode
    fullspan::Int
    span::Int
    kind::Tokenize.Tokens.Kind
    dot::Bool
    meta::Meta
    OPERATOR(fullspan::Int, span::Int, kind::Tokenize.Tokens.Kind, dot::Bool, meta::Meta) = new(fullspan, span, kind, dot, meta)
end
@noinline OPERATOR(fullspan::Int, span::Int, kind::Tokenize.Tokens.Kind, dot::Bool) = OPERATOR(fullspan, span, kind, dot, Meta())
@noinline OPERATOR(ps::ParseState) = OPERATOR(ps.nt.startbyte - ps.t.startbyte, ps.t.endbyte - ps.t.startbyte + 1, ps.t.kind, ps.t.dotop)

struct KEYWORD <: LeafNode
    kind::Tokenize.Tokens.Kind
    fullspan::Int
    span::Int
    meta::Meta
    KEYWORD(kind::Tokenize.Tokens.Kind, fullspan::Int, span::Int, meta::Meta) = new(kind, fullspan, span, meta)
end
@noinline KEYWORD(kind::Tokenize.Tokens.Kind, fullspan::Int, span::Int) = KEYWORD(kind, fullspan, span, Meta())
@noinline KEYWORD(ps::ParseState) = KEYWORD(ps.t.kind, ps.nt.startbyte - ps.t.startbyte, ps.t.endbyte - ps.t.startbyte + 1)


struct LITERAL <: LeafNode
    fullspan::Int
    span::Int
    val::String
    kind::Tokenize.Tokens.Kind
    meta::Meta
    LITERAL(fullspan::Int, span::Int, val::String, kind::Tokenize.Tokens.Kind, meta::Meta) = new(fullspan, span, val, kind, meta)
end
LITERAL(fullspan::Int, span::Int, val::String, kind::Tokenize.Tokens.Kind) = LITERAL(fullspan, span, val, kind, Meta())
function LITERAL(ps::ParseState)
    if ps.t.kind == Tokens.STRING || ps.t.kind == Tokens.TRIPLE_STRING ||
       ps.t.kind == Tokens.CMD || ps.t.kind == Tokens.TRIPLE_CMD
        return parse_string_or_cmd(ps)
    else
        LITERAL(ps.nt.startbyte - ps.t.startbyte, ps.t.endbyte - ps.t.startbyte + 1, val(ps.t, ps), ps.t.kind)
    end
end

# AbstractTrees.children(x::EXPR) = x.args

span(x::AbstractEXPR) = x.span

function update_span!(x) end
function update_span!(x::EXPR)
    isempty(x.args) && return
    x.fullspan = 0
    for a in x.args
        x.fullspan += a.fullspan
    end
    x.span = x.fullspan - last(x.args).fullspan + last(x.args).span
    return 
end

function Base.push!(e::EXPR, arg)
    e.span = e.fullspan + arg.span
    e.fullspan += arg.fullspan
    setparent!(arg, e)
    push!(e.args, arg)
end

function Base.pushfirst!(e::EXPR, arg)
    e.fullspan += arg.fullspan
    setparent!(arg, e)
    pushfirst!(e.args, arg)
end

function Base.pop!(e::EXPR)
    arg = pop!(e.args)
    e.fullspan -= arg.fullspan
    if isempty(e.args)
        e.span = 0
    else
        e.span = e.fullspan - last(e.args).fullspan + last(e.args).span
    end
    arg
end

function Base.append!(e::EXPR, args::Vector)
    for a in args 
        setparent!(a, e)
    end
    append!(e.args, args)
    update_span!(e)
end

function Base.append!(a::EXPR, b::EXPR)
    append!(a.args, b.args)
    for arg in b.args 
        setparent!(arg, a)
    end
    a.fullspan += b.fullspan
    a.span = a.fullspan + last(b.span)
end

function Base.append!(a::EXPR, b::KEYWORD)
    append!(a.args, b.args)
    a.fullspan += b.fullspan
    a.span = a.fullspan + last(b.span)
end

function INSTANCE(ps::ParseState)
    if isidentifier(ps.t)
        return IDENTIFIER(ps)
    elseif isliteral(ps.t)
        return LITERAL(ps)
    elseif iskw(ps.t)
        return KEYWORD(ps)
    elseif isoperator(ps.t)
        return OPERATOR(ps)
    elseif ispunctuation(ps.t)
        return PUNCTUATION(ps)
    else
        return ErrorToken()
    end
end


mutable struct File
    imports
    includes::Vector{Tuple{String,Any}}
    path::String
    ast::EXPR
    errors
end
File(path::String) = File([], [], path, EXPR{FileH}(Any[]), [])

mutable struct Project
    path::String
    files::Vector{File}
end

abstract type Head end
abstract type Call <: Head end

mutable struct UnaryOpCall <: AbstractEXPR
    op::OPERATOR
    arg
    fullspan::Int
    span::Int
    meta::Meta
    function UnaryOpCall(op, arg)
        fullspan = op.fullspan + arg.fullspan
        out = new(op, arg, fullspan, fullspan - arg.fullspan + arg.span, Meta())
        setparent!(out.op, out)
        setparent!(out.arg, out)
        return out
    end
end

mutable struct UnarySyntaxOpCall <: AbstractEXPR
    arg1
    arg2
    fullspan::Int
    span::Int
    meta::Meta
    function UnarySyntaxOpCall(arg1, arg2)
        fullspan = arg1.fullspan + arg2.fullspan
        out = new(arg1, arg2, fullspan, fullspan - arg2.fullspan + arg2.span, Meta())
        setparent!(out.arg1, out)
        setparent!(out.arg2, out)
        return out
    end
end

mutable struct BinaryOpCall <: AbstractEXPR
    arg1
    op::OPERATOR
    arg2
    fullspan::Int
    span::Int
    meta::Meta
    function BinaryOpCall(arg1, op, arg2)
        fullspan = arg1.fullspan + op.fullspan + arg2.fullspan
        out = new(arg1, op, arg2, fullspan, fullspan - arg2.fullspan + arg2.span, Meta())
        setparent!(out.arg1, out)
        setparent!(out.op, out)
        setparent!(out.arg2, out)
        return out
    end
end

mutable struct BinarySyntaxOpCall <: AbstractEXPR
    arg1
    op::OPERATOR
    arg2
    fullspan::Int
    span::Int
    meta::Meta
    function BinarySyntaxOpCall(arg1, op, arg2)
        fullspan = arg1.fullspan + op.fullspan + arg2.fullspan
        out = new(arg1, op, arg2, fullspan, fullspan - arg2.fullspan + arg2.span, Meta())
        setparent!(out.arg1, out)
        setparent!(out.op, out)
        setparent!(out.arg2, out)
        return out
    end
end

mutable struct WhereOpCall <: AbstractEXPR
    arg1
    op::OPERATOR
    args::Vector
    fullspan::Int
    span::Int
    meta::Meta
    function WhereOpCall(arg1, op::OPERATOR, args)
        out = new(arg1, op, args, arg1.fullspan + op.fullspan, - last(args).fullspan + last(args).span, Meta())
        setparent!(out.arg1, out)
        setparent!(out.op, out)
        for a in args
            setparent!(a, out)
            out.fullspan += a.fullspan
        end
        out.span += out.fullspan
        return out
    end
end

mutable struct ConditionalOpCall <: AbstractEXPR
    cond
    op1::OPERATOR
    arg1
    op2::OPERATOR
    arg2
    fullspan::Int
    span::Int
    meta::Meta
    function ConditionalOpCall(cond, op1, arg1, op2, arg2)
        fullspan = cond.fullspan + op1.fullspan + arg1.fullspan + op2.fullspan + arg2.fullspan
        out = new(cond, op1, arg1, op2, arg2, fullspan, fullspan - arg2.fullspan + arg2.span, Meta())
        setparent!(out.cond, out)
        setparent!(out.op1, out)
        setparent!(out.arg1, out)
        setparent!(out.op2, out)
        setparent!(out.arg2, out)
        return out
    end
end

abstract type ChainOpCall <: Head end
abstract type ColonOpCall <: Head end
abstract type Abstract <: Head end
abstract type Begin <: Head end
abstract type Block <: Head end
abstract type Braces <: Head end
abstract type BracesCat <: Head end
abstract type Const <: Head end
abstract type Comparison <: Head end
abstract type Curly <: Head end
abstract type Do <: Head end
abstract type Filter <: Head end
abstract type Flatten <: Head end
abstract type For <: Head end
abstract type FunctionDef <: Head end
abstract type Generator <: Head end
abstract type Global <: Head end
abstract type GlobalRefDoc <: Head end
abstract type If <: Head end
abstract type Kw <: Head end
abstract type Let <: Head end
abstract type Local <: Head end
abstract type Macro <: Head end
abstract type MacroCall <: Head end
abstract type MacroName <: Head end
abstract type Mutable <: Head end
abstract type Outer <: Head end
abstract type Parameters <: Head end
abstract type Primitive <: Head end
abstract type Quote <: Head end
abstract type Quotenode <: Head end
abstract type InvisBrackets <: Head end
abstract type StringH <: Head end
abstract type Struct <: Head end
abstract type Try <: Head end
abstract type TupleH <: Head end
abstract type FileH <: Head end
abstract type Return <: Head end
abstract type While <: Head end
abstract type x_Cmd <: Head end
abstract type x_Str <: Head end

abstract type ModuleH <: Head end
abstract type BareModule <: Head end
abstract type TopLevel <: Head end
abstract type Export <: Head end
abstract type Import <: Head end
abstract type ImportAll <: Head end
abstract type Using <: Head end

abstract type Comprehension <: Head end
abstract type DictComprehension <: Head end
abstract type TypedComprehension <: Head end
abstract type Hcat <: Head end
abstract type TypedHcat <: Head end
abstract type Ref <: Head end
abstract type Row <: Head end
abstract type Vcat <: Head end
abstract type TypedVcat <: Head end
abstract type Vect <: Head end

abstract type ErrorToken <: Head end
ErrorToken() = EXPR{ErrorToken}(Any[], 0, 0)
ErrorToken(x) = EXPR{ErrorToken}(Any[x])

Quotenode(x) = EXPR{Quotenode}(Any[x])

TRUE() = LITERAL(0, 0, "", Tokens.TRUE)
FALSE() = LITERAL(0, 0, "", Tokens.FALSE)
NOTHING() = LITERAL(0, 0, "", Tokens.NOTHING)
GlobalRefDOC() = EXPR{GlobalRefDoc}(Any[], 0, 0)


getparent(c::T) where T <: Union{EXPR,IDENTIFIER,KEYWORD,PUNCTUATION,OPERATOR,LITERAL,UnaryOpCall,UnarySyntaxOpCall,BinaryOpCall,BinarySyntaxOpCall,WhereOpCall,ConditionalOpCall} = c.meta.parent

function setparent!(c::T, p) where T <: Union{EXPR,IDENTIFIER,KEYWORD,PUNCTUATION,OPERATOR,LITERAL,UnaryOpCall,UnarySyntaxOpCall,BinaryOpCall,BinarySyntaxOpCall,WhereOpCall,ConditionalOpCall}
    c.meta.parent = p
    return c
end

function setparent!(c, p) return c end

function finalize_expr!(x)
    for a in x
        if a <: Union{EXPR,IDENTIFIER,PUNCTUATION,OPERATOR,KEYWORD}
            setparent!(a, x)
        end
    end
    return x
end


@generated function make_expr(head, args::NTuple{N,Any}) where N
    fs = Expr(:call, :+)
    eargs = :(Any[])
    for i = 1:N
        push!(fs.args, :(args[$i].fullspan))
        push!(eargs.args, :(args[$i]))
    end
    ex = quote
        fullspan = $fs
        ret = EXPR{head}($eargs, fullspan, fullspan - (args[$N].fullspan - args[$N].span), Meta())
    end
    for i = 1:N
        push!(ex.args, :(setparent!(args[$i], ret)))
    end
    push!(ex.args, :(return ret))
    ex
end 

@generated function make_expr(head, args::NTuple{N,Any}, fullspan::Int, span::Int) where N
    eargs = :(Any[])
    for i = 1:N
        push!(eargs.args, :(args[$i]))
    end
    ex = quote
        ret = EXPR{head}($eargs, fullspan, span, Meta())
    end
    for i = 1:N
        push!(ex.args, :(setparent!(args[$i], ret)))
    end
    push!(ex.args, :(return ret))
    ex
end 
