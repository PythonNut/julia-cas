import Base.print
import Base.show
import Base.string

abstract Exp

Binary = Union()

macro binary_operator(T, operator, symbol)
    quote
        type $T <: Exp
            l::Exp
            r::Exp

            # metadata
            data::Dict{Any,Any}

            # operator in function form
            op

            $(esc(T))(l::Exp, r::Exp) = new(l, r, Dict{Any,Any}(), $operator)
        end

        # conversion to string
        global string(x::$(esc(T))) = "$(string_wrap(x.l)) " * $symbol * " $(string_wrap(x.r))"
        global string_wrap(x::$(esc(T))) = "($(string(x)))"

        # hash
        global hash(x::$(esc(T))) = hash(hash(x.l) + hash(x.r))

        # define as an operator overload
        global $(esc(operator))(a::Exp, b::Exp) = $T(a, b)

        # add to Binary type union
        global Binary = Union(Binary,$(esc(T)))
    end
end

Unary = Union()

macro unary_operator(T, func, symbol)
    quote
        type $T <: Exp
            x::Exp

            # metadata
            data::Dict{Any,Any}

            # operation in function form
            op

            $(esc(T))(x::Exp) = new(x, Dict{Any,Any}(), $func)
        end

        global hash(x::$(esc(T))) = hash(hash(x.x))

        global string_wrap(x::$(esc(T))) = string(x)
        global $(esc(func))(x::Exp) = $T(x)
        global Unary = Union($Unary,$(esc(T)))
    end
end

# ==========================
# begin operator definitions
# ==========================

@binary_operator(Add,+,"+")
@binary_operator(Sub,-,"-")
@binary_operator(Mul,*,"*")
@binary_operator(Div,/,"/")
@binary_operator(Pow,^,"^")

type Num <: Exp
    x::Int64

    # general metadata field
    data::Dict{Any,Any}
    Num(x) = new(x, Dict{Any,Any}())
end

string(x::Num) = "u$(string(x.x))"
string_wrap(x::Num) = string(x)

@unary_operator(Neg,-,"-")
string(x::Neg) = "-($(string(x.x)))"

# Symbols (aka. variables)
type Sym <: Exp
    x::ASCIIString

    # a symbol metadata field
    class::ASCIIString

    # general metadata field
    data::Dict{Any,Any}

    Sym(x) = new(x,"",Dict{Any,Any}())
    Sym(x,class) = new(x, class, Dict{Any,Any}())
end

string(x::Sym) = x.x
hash(x::Sym) = hash(hash(x.x) + hash(x.class))


# begin general expression functions

print(io::IO, x::Exp) = print(io, string(x))
show(io::IO, x::Exp) = print(io, x)
string_wrap(x::Exp) = string(x)

type Inference
    this::Exp
    that::Exp
end

string(x::Inference) = "$(x.this) ==> $(x.that)"

type Eval <: Exp
    x::Exp

    # general metadata field
    data::Dict{Any,Any}
    Eval(x) = new(x, Dict{Any,Any}())
end

string(x::Eval) = "eval($(string(x.x)))"

print(io::IO, x::Inference) = print(io, string(x))
show(io::IO, x::Inference) = print(io, x)

Atom = Union(Sym, Num)
hash(x::Binary) = hash(hash(x.l) + hash(x.r))
hash(x::Union(Unary,Num)) = hash(hash(x.x))

# define strict equality
isequal{T<:Binary}(a::T, b::T) = (a.l == b.l) & (a.r == b.r)
isequal{T<:Union(Unary,Num)}(a::T, b::T) = a.x == b.x
isequal(a::Sym, b::Sym) = (a.x == b.x) & (a.class == b.class)
==(a::Exp, b::Exp) = isequal(a, b)

convert(::Type{Num}, x::Int64) = Num(x)
convert(::Type{Exp}, x::Int64) = Num(x)

# check a pattern, but take symbols into account
equals(a,b) = false
equals{T<:Binary}(a::T, b::T) = equals(a.l, b.l) & equals(a.r, b.r)
equals{T<:Unary}(a::T, b::T) = equals(a.x, b.x)
equals{T<:Num}(a::T, b::T) = a == b
equals(a::Exp, b::Sym) = true

macro s_str(s)
    Sym(s)
end

macro S_str(s)
    Sym(s,"inference")
end

# merge two symbol descriptors
function merge(a::Dict{Sym,Set{Exp}}, b::Dict{Sym,Set{Exp}})
    result = a
    for (k, v) in b
        if haskey(result, k)
            result[k] = union(result[k], v)
        else
            result[k] = v
        end
    end
    return result
end

symbols(a,b) = Dict{Sym,Set{Exp}}()
symbols{T<:Binary}(a::T, b::T) = merge(symbols(a.l, b.l), symbols(a.r, b.r))
symbols(e::Exp, i::Inference) = symbols(e, i.this)
symbols{T<:Union(Neg,Eval)}(a::T, b::T) = symbols(a.x, b.x)
symbols(a::Exp, b::Sym) = Dict(b => Set{Exp}([a]))

subs{T<:Binary}(x::T, s::Sym, e::Exp) = T(subs(x.l, s, e), subs(x.r, s, e))
subs{T<:Unary}(x::T, s::Sym, e::Exp) = T(subs(x.x, s, e))
subs(x, s::Sym, e::Exp) = x
subs(x::Num, s::Sym, e::Exp) = x
subs(x::Sym, s::Sym, e::Exp) = x == s ? e : x
subs(x::Eval, s::Sym, e::Exp) = Eval(subs(x.x, s, e))

function eval_expr{T<:Binary}(x::T, ev::Bool = false)
    l = eval_expr(x.l, ev)
    r = eval_expr(x.r, ev)
    if ev & (typeof(l) == typeof(r) == Num)
        return Num(x.op(l.x,r.x))
    end
    return T(l, r)
end

function eval_expr{T<:Unary}(x::T, ev::Bool = false)
    x = eval_expr(x.x, ev)
    if ev & (typeof(x) == Num)
        return Num(x.op(x.x))
    end
    return T(x)
end

eval_expr(x::Eval, ev::Bool = false) = eval_expr(x.x, true)
eval_expr(x::Atom, ev::Bool = false) = x


applies(e::Exp, i::Inference) = applies(e, i.this)
function applies(e::Exp, i::Exp)
    if equals(e, i)
        syms = symbols(e, i)
        return all([length(v) == 1 for (_,v) in syms])
    end
    return false
end

function apply(e::Exp, inf::Inference)
    if applies(e, inf)
        result = inf.that
        syms = symbols(e, inf)
        for (k,v) in syms
            result = subs(result, k, collect(v)[1])
        end
        return eval_expr(result)
    end
    return e
end

map{T<:Binary}(x::T, f) = f(T(map(x.l, f),map(x.r, f)))
map{T<:Unary}(x::T, f) = f(T(map(x.x, f)))
map(x::Eval, f) = f(Eval(map(x.x, f)))
map(x::Atom, f) = f(x)

function applicable_lambda(x::Exp, i::Inference)
    x.data["applies"] = applies(x, i)
    return x
end

function applicable(x::Exp, i::Inference)
    return map(x, e -> applicable_lambda(e, i))
end

rules = Inference[]
push!(rules, Inference(S"x" + -S"y", S"x" - S"y"))
push!(rules, Inference(S"a" * S"x" + S"b" * S"x", Eval(S"a" + S"b") * S"x"))

# distributive property of addition
push!(rules, Inference((S"a" + S"b") * S"c", S"a" * S"c" + S"b" * S"c"))

# commutative property of addition and multiplication
push!(rules, Inference(S"a" + S"b", S"b" + S"a"))
push!(rules, Inference(S"a" * S"b", S"b" * S"a"))

# associative property of addition and multiplication
push!(rules, Inference((S"x" + S"y") + S"z", S"x" + (S"y" + S"z")))
push!(rules, Inference((S"x" * S"y") * S"z", S"x" * (S"y" * S"z")))

# exponentiation rules
push!(rules, Inference(S"x" ^ S"y" , S"x" ^ Eval(S"y" - Num(1)) * S"x"))
