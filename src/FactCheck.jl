######################################################################
# FactCheck.jl
# A testing framework for Julia
# http://github.com/JuliaLang/FactCheck.jl
# MIT Licensed
######################################################################

module FactCheck

export @fact, @fact_throws, @pending,
       facts, context,
       # Assertion helpers
       not,
       exactly,
       roughly,
       anyof,
       less_than, less_than_or_equal,
       greater_than, greater_than_or_equal

######################################################################
# Success, Failure, Error <: Result
# Represents the result of a test. These are very similar to the types
# with the same names in Base.Test, except for the addition of the
# `ResultMetadata` type that is used to retain information about the test,
# such as its file, line number, description, etc.
abstract type Result end

mutable struct ResultMetadata
    line
    msg
    function ResultMetadata(;line=nothing, msg=nothing)
        new(line, msg)
    end
end

mutable struct Success <: Result
    expr::Expr
    fact_type::Symbol
    lhs  # What it was
    rhs  # What it should have been
    meta::ResultMetadata
end

mutable struct Failure <: Result
    expr::Expr
    fact_type::Symbol
    lhs  # What it was
    rhs  # What it should have been
    meta::ResultMetadata
end

mutable struct Error <: Result
    expr::Expr
    fact_type::Symbol
    err::Exception
    backtrace
    meta::ResultMetadata
end

struct Pending <: Result end

# Collection of all results across facts
allresults = Result[]
clear_results() = (global allresults; allresults = Result[])

# Formats a fact expression
function format_fact(ex::Expr)
    if ex.head == :(-->) || ex.head == :(=>)
        # :(fn(1) --> 2) to 'fn(1) --> 2'
        # :("1"*"1" --> "11") to '"1" * "1" --> "11"'
        # We handle non-expresion arguments differently,
        # otherwise, e.g. quote marks on strings disappear
        x, y = ex.args
        x_str = sprint(isa(x,Expr) || isa(x,Symbol) ? print : show, x)
        y_str = sprint(isa(y,Expr) || isa(y,Symbol) ? print : show, y)
        string(x_str, " --> ", y_str)
    else
        # Something else, that maybe didn't have a -->
        # such as @fact_throws. Punt and just stringify
        string(ex)
    end
end

# Define printing functions for the result types
function Base.show(io::IO, f::Failure)
    println(io, "\n<IT::>", replace_lf(format_fact(f.expr)))
    print(io, "\n<FAILED::>", replace_lf(f.meta.msg != nothing ? "$(f.meta.msg)" : "Test Failed"))
    if f.fact_type == :fact_throws
        # @fact_throws didn't get an error, or the right type of error
        if f.rhs != :fact_throws_noerror
            print(io, "<:LF:>  Expected: ", f.rhs[1])
            print(io, "<:LF:>  Occurred: ", f.rhs[2])
        end
    elseif f.fact_type == :fact
        # @fact didn't get the right result
        args = f.expr.args
        if length(args) >= 2 && _factcheck_function(args[2]) != nothing
            # Fancy helper fact
            fcFunc = _factcheck_function(args[2])
            if haskey(FACTCHECK_FUN_NAMES, fcFunc)
                print(io, replace_lf(string("<:LF:>  Expected: ", sprint(show, f.lhs), " ", FACTCHECK_FUN_NAMES[fcFunc], " ", sprint(show, f.rhs))))
            else
                print(io, replace_lf(string("<:LF:>  Expected: ", sprint(show, f.lhs), " --> ", fcFunc, "(", sprint(show, f.rhs), ")")))
            end
        else
            # Normal equality-test-style fact
            print(io, replace_lf(string("<:LF:>  Expected: ", sprint(show, f.rhs), "<:LF:>  Occurred: ", sprint(show, f.lhs))))
        end
    else
        error("Unknown fact type: ", f.fact_type)
    end
    println(io, "\n\n<COMPLETEDIN::>")
end

function Base.show(io::IO, e::Error)
    println(io, "\n<IT::>", replace_lf(e.meta.msg != nothing ? "$(e.meta.msg)" : format_fact(e.expr)))
    println(io, "\n<ERROR::>", replace_lf(sprint(showerror, e.err)))
    println(io, "\n<LOG::-Stack trace>", replace_lf(sprint(showerror, e.err, e.backtrace)))
    println(io, "\n<COMPLETEDIN::>")
end

function Base.show(io::IO, s::Success)
	println(io, "\n<IT::>", replace_lf(format_fact(s.expr)))
	println(io, "\n<PASSED::>Test Passed")
	println(io, "\n<COMPLETEDIN::>")
end

function Base.show(io::IO, ::Pending)
    println(io, "\n<LOG::>Pending")
end

const SPECIAL_FACTCHECK_FUNCTIONS =
    Set([:not, :exactly, :roughly, :anyof,
         :less_than, :less_than_or_equal, :greater_than, :greater_than_or_equal])

const FACTCHECK_FUN_NAMES =
    Dict{Symbol,AbstractString}(
      :roughly => "≅",
      :less_than => "<",
      :less_than_or_equal => "≤",
      :greater_than => ">",
      :greater_than_or_equal => "≥")

isexpr(x) = isa(x, Expr)
iscallexpr(x) = isexpr(x) && x.head == :call
isdotexpr(x) = isexpr(x) && x.head == :.
isquoteexpr(x) = isexpr(x) && x.head == :quote
isparametersexpr(x) = isexpr(x) && x.head == :parameters

function _factcheck_function(assertion)
    iscallexpr(assertion) || return nothing

    # checking for lhs => roughly(rhs)
    if assertion.args[1] in SPECIAL_FACTCHECK_FUNCTIONS
        return assertion.args[1]
    end

    # checking for lhs => FactCheck.roughly(rhs)
    isdotexpr(assertion.args[1]) || return nothing
    dotexpr = assertion.args[1]
    length(dotexpr.args) >= 2 || return nothing
    if isquoteexpr(dotexpr.args[2])
        quoteexpr = dotexpr.args[2]
        if length(quoteexpr.args) >= 1 && quoteexpr.args[1] in SPECIAL_FACTCHECK_FUNCTIONS
            return quoteexpr.args[1]
        else
            return nothing
        end
    end

    # sometimes it shows up as a QuoteNode...
    if isa(dotexpr.args[2], QuoteNode) && dotexpr.args[2].value in SPECIAL_FACTCHECK_FUNCTIONS
        return dotexpr.args[2].value
    end
    nothing
end


######################################################################
# Core testing macros and functions

# @fact takes an assertion of the form LHS --> RHS, and replaces it
# with code to evaluate that fact (depending on the type of the RHS),
# and produce and record a result based on the outcome
macro fact(factex::Expr, args...)
    if factex.head != :(-->) && factex.head != :(=>)
        error("Incorrect usage of @fact: $factex")
    end
    # TODO: remove deprecated syntax
    if factex.head == :(=>)
        Base.warn_once("The `=>` syntax is deprecated, use `-->` instead")
    end
    # Extract the two sides of the fact
    lhs, initial_rhs = factex.args
    # If there is another argument to the macro, assume it is a
    # message and record it
    msg = length(args) > 0 ? args[1] : (:nothing)

    # rhs is the assertion, unless it's wrapped by a special FactCheck function
    rhs = initial_rhs
    if _factcheck_function(initial_rhs) != nothing
        rhs = initial_rhs.args[isparametersexpr(initial_rhs.args[2]) ? 3 : 2]
    end

    quote
        # Build a function (predicate) that, depending on the nature of
        # the RHS, either compares the sides or applies the RHS to the LHS
        predicate = function(lhs_value)
            rhs_value = $(esc(initial_rhs))
            if isa(rhs_value, Function)
                # The RHS is a function, so instead of testing for equality,
                # return the value of applying the RHS to the LHS
                (rhs_value(lhs_value), lhs_value, $(esc(rhs)))
            else
                # The RHS is a value, so test for equality
                (rhs_value == lhs_value, lhs_value, $(esc(rhs)))
            end
        end
        # Replace @fact with a call to the do_fact function that constructs
        # the test result object by evaluating the
        do_fact(() -> predicate($(esc(lhs))),
                $(Expr(:quote, factex)),
                :fact,
                ResultMetadata(line=getline(),
                               msg=$(esc(msg))))
    end
end

# `@fact_throws` is similar to `@fact`, except it only checks if
# the expression throws an error or not - there is no explict
# assertion to compare against.
macro fact_throws(args...)
    expr, extype, msg = nothing, nothing, nothing
    nargs = length(args)
    if nargs == 1
        if isa(args[1],Expr)
            expr = args[1]
        else
            throw(ArgumentError("invalid @fact_throws macro"))
        end
    elseif nargs == 2
        if (isa(args[1],Symbol) || isa(args[1],Expr)) && isa(args[2],Expr)
            extype, expr = args
        elseif isa(args[1],Expr)
            expr, msg = args
        else
            throw(ArgumentError("invalid @fact_throws macro"))
        end
    elseif nargs >= 3
        if (isa(args[1],Symbol) || isa(args[1], Expr)) && isa(args[2],Expr)
            extype, expr, msg = args
        else
            throw(ArgumentError("invalid @fact_throws macro"))
        end
    end

    quote
        do_fact(() -> try
                          $(esc(expr))
                          (false, "no exception was thrown", :fact_throws_noerror)
                      catch ex
                          $(if extype === nothing
                              :((true, "an exception was thrown", :fact_throws_error))
                            else
                              :(if isa(ex,$(esc(extype)))
                                  (true, "correct exception was thrown", :fact_throws_error)
                                else
                                  (false, "wrong exception was thrown",
                                    ($(esc(extype)), typeof(ex)))
                                end)
                            end)
                      end,
                $(Expr(:quote, expr)),
                :fact_throws,
                ResultMetadata(line=getline(),msg=$(esc(msg))))
    end
end

# `do_fact` constructs a Success, Failure, or Error depending on the
# outcome of a test and passes it off to the active test handler
# `FactCheck.handlers[end]`. It finally returns the test result.
function do_fact(thunk::Function, factex::Expr, fact_type::Symbol, meta::ResultMetadata)
    result = try
        res, val, rhs = thunk()
        res ? Success(factex, fact_type, val, rhs, meta) :
                Failure(factex, fact_type, val, rhs, meta)
    catch err
        Error(factex, fact_type, err, catch_backtrace(), meta)
    end

    !isempty(handlers) && handlers[end](result)
    result
end

# `@pending` is a no-op test - it doesn't do anything except record
# its existance in the final totals of tests "run"
macro pending(factex::Expr, args...)
    quote
        result = Pending()
        !isempty(handlers) && handlers[end](result)
        result
    end
end

######################################################################
# Grouping of tests
#
# `facts` describes a top-level test scope, which can contain
# `contexts` to group similar tests. Test results will be collected
# instead of throwing an exception immediately.

# A TestSuite collects the results of a series of tests, as well as
# some information about the tests such as their file and description.
mutable struct TestSuite
    filename
    desc
    successes::Vector{Success}
    failures::Vector{Failure}
    errors::Vector{Error}
    pending::Vector{Pending}
end
TestSuite(f, d) = TestSuite(f, d, Success[], Failure[], Error[], Pending[])

# The last handler function found in `handlers` will be passed
# test results.
const handlers = Function[]

# A list of test contexts. `contexts[end]` should be the
# inner-most context.
const contexts = AbstractString[]

# Constructs a function that handles Successes, Failures, and Errors,
# pushing them into a given TestSuite and printing Failures and Errors
# as they arrive (unless in compact mode, in which case we delay
# printing details until the end).
function make_handler(suite::TestSuite)
    function delayed_handler(r::Success)
        print(r)
    end
    function delayed_handler(r::Failure)
        print(r)
    end
    function delayed_handler(r::Error)
        print(r)
    end
    function delayed_handler(r::Pending)
        print(r)
    end
    delayed_handler
end

# facts
# Creates testing scope. It is responsible for setting up a testing
# environment, which means constructing a `TestSuite`, generating
# and registering test handlers, and reporting results.
function facts(f::Function, desc)
    println(string("\n<DESCRIBE::>", replace_lf(desc == nothing ? "Unnamed Facts" : "$(desc)")))
    handler = make_handler(TestSuite(nothing, desc))
    push!(handlers, handler)
    f()
    pop!(handlers)
    println("\n<COMPLETEDIN::>")
end
facts(f::Function) = facts(f, nothing)

# context
# Executes a battery of tests in some descriptive context, intended
# for use inside of `facts`. Displays the string in default mode.
function context(f::Function, desc::AbstractString)
    println(string("\n<DESCRIBE::>", replace_lf(desc == "" ? "Unnamed Context" : desc)))
    push!(contexts, desc)
    try
        f()
    finally
        pop!(contexts)
        println("\n<COMPLETEDIN::>")
    end
end
context(f::Function) = context(f, "")

######################################################################

@noinline getline() = StackTraces.stacktrace()[2].line

replace_lf(s::AbstractString) = replace(s, "\n" => "<:LF:>")

############################################################
# Assertion helpers
include("helpers.jl")


end # module FactCheck
