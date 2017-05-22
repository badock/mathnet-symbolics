namespace MathNet.Symbolics

open MathNet.Symbolics
open Operators

[<RequireQualifiedAccess>]
module Calculus =

    [<CompiledName("Differentiate")>]
    let rec differentiate symbol = function
        | x when x = symbol -> one
        | Undefined as x -> x
        | Number _ | Approximation _ | Identifier _ | Constant _ | ComplexInfinity | PositiveInfinity | NegativeInfinity -> zero
        | Sum xs -> sum <| List.map (differentiate symbol) xs
        | Product [x] -> differentiate symbol x
        | Product (x::xs) ->
            let dx = differentiate symbol x
            let dxs = differentiate symbol (Product xs)
            x*dxs + (product xs)*dx
        | Power (r, e) as p ->
            let dr = differentiate symbol r
            let de = differentiate symbol e
            de*ln(r)*p + e*dr*(r**(e-1))
        | Function (Exp, x) as f -> (differentiate symbol x) * f
        | Function (Ln, x) -> (differentiate symbol x) / x
        | Function (Sin, x) -> (differentiate symbol x) * cos(x)
        | Function (Cos, x) -> -(differentiate symbol x) * sin(x)
        | Function (Tan, x) -> 2*(differentiate symbol x) / (cos(2*x)+1)
        | Function (Cosh, x) -> (differentiate symbol x) * sinh (x)
        | Function (Sinh, x) -> (differentiate symbol x) * cosh (x)
        | Function (Tanh, x) -> 2*(differentiate symbol x) / (cosh(2*x)+1)
        | Function (Asin, x) -> (1Q/sqrt(1Q+pow x 2Q)) * (differentiate symbol x)
        | Function (Acos, x) -> (-1Q/sqrt(1Q+pow x 2Q)) * (differentiate symbol x)
        | Function (Atan, x) -> (1Q/1Q+pow x 2Q) * (differentiate symbol x)
        | Function (Cot, x) -> (-1Q/(sin(x) * sin(x))) * (differentiate symbol x)
        | Function (Csc, x) -> (-cot(x) * csc(x)) * (differentiate symbol x)
        | Function (Sec, x) -> (tan(x) * sec(x)) * (differentiate symbol x)
        | FunctionN (f, xs) -> failwith "not supported"
        | Function (Abs, _) -> failwith "not supported"
        | Product [] -> failwith "invalid expression"

    /// Differentiate expression to symbol and substitute symbol with value
    [<CompiledName("DifferentiateAt")>]
    let differentiateAt symbol value expression =
        expression |> differentiate symbol |> Structure.substitute symbol value

    [<CompiledName("MatchPowerRule")>]
    let match_power_rule s f g =
        let df = differentiate s f
        if g = df then
            true
        else
            false

    let match_sine_integral_rule s fg =
        match fg with
            | Function(Sin, s) :: Power(symbol, n) :: [] -> n.Equals(number -1)
            | Power(symbol, n) :: Function(Sin, s) :: [] -> n.Equals(number -1)
            | _ -> false

    let rec elements_to_product l = 
        match l with
            | x :: xs -> 
                let xs_as_product = elements_to_product xs
                x * xs_as_product
            | [] -> number 1
   
    exception ApplyLinearityRuleException of Expression * Expression * Expression

    let rec last = function
        | hd :: [] -> hd
        | hd :: tl -> last tl
        | _ -> failwith "Empty list."

    let rec antidifferentiate_rec s l = function
        | x when x = s -> number 1 /  number 2 * s * s
        | Undefined as x -> failwith "not implemented (1)"
        | Number num as n when num.IsZero -> 
            printfn "1>Number:"
            number 0
        | Number num as n when not num.IsZero -> n * s
        | Approximation approx -> failwith "not implemented (3)"
        | Identifier ident as a -> a * s
        | Constant cons -> failwith "not implemented (5)"
        | Sum xs -> failwith "not implemented (6)"
        | Product _ as p -> integration_product s l p
        | Power (r, Number num) as p when Number num = number -1 -> 
            printfn "1>power:"
            Function (Ln, r)
        | Power (r, Number num) as p when Number num = number -2 -> 
            printfn "2>power:"
            number -1 * Power(r, number -1)
        | Power (r, Number num) as p when not num.IsPositive -> 
            printfn "3>power:"
            number 1 / ((Number num + number 1) * Power(r, (number -1 * Number num) - number 1))
        | Power (r, e) as p -> e
        | Function (Exp, x) as f -> (s/x) * f
        | Function (Ln, x) -> s * Function(Ln, x) - s
        | Function (Sin, x) -> (s/x) * number -1 * Function (Cos, x)//failwith "not implemented (11)"os, x)
        | Function (Cos, x) -> (s/x) * Function (Sin, x)
        | Function (Tan, x) -> (s/x) * number -1 * Function(Ln, Function(Cos, x))
        | Function (Cosh, x) -> (s/x) * Function(Sinh, x)
        | Function (Sinh, x) -> (s/x) * Function(Cosh, x)
        | Function (Tanh, x) -> (s/x) * Function(Ln, Function(Cosh, x))
        | Function (Asin, x) -> failwith "not implemented (18)"
        | Function (Acos, x) -> failwith "not implemented (19)"
        | Function (Atan, x) -> failwith "not implemented (20)"
        | Function (Cot, x) -> failwith "not implemented (21)"
        | Function (Csc, x) -> failwith "not implemented (22)"
        | Function (Sec, x) -> failwith "not implemented (23)"
        | FunctionN (f, xs) -> failwith "not supported"
        | Function (Abs, _) -> failwith "not supported"
        | ComplexInfinity | PositiveInfinity | NegativeInfinity -> failwith "not supported"
        | Product [] -> failwith "invalid expression"

    and integration_product s l = function
        | Product (Number num :: xs) ->
            printfn "1>product: x: {%s * %s, d%s}" (num.ToString()) (xs.ToString()) (s.ToString())
            let xs_product = elements_to_product xs
            try
                Number num * antidifferentiate_rec s l xs_product
            with
                | ApplyLinearityRuleException (n, e, t) -> raise(ApplyLinearityRuleException (n, Number num * e, t))
        | Product (x :: [Number num]) ->
            printfn "2>product: x: {%s * %s}" (num.ToString()) (x.ToString())         
            Number num * antidifferentiate_rec s l x
        | Product (x::xs) when match_power_rule s x (elements_to_product xs) ->
            printfn "3>product: x: {%s * %s}" (x.ToString()) (xs.ToString()) 
            Power(x, number 2) / 2
        | Product (x::xs) when match_power_rule s (elements_to_product xs) x ->
            printfn "4>product: x: {%s * %s}" (x.ToString()) (xs.ToString()) 
            Power((elements_to_product xs), number 2) / 2
        | Product (x::xs) when match_sine_integral_rule s (x::xs) ->
            printfn "5>product: x: {%s * %s}" (x.ToString()) (xs.ToString()) 
            Function(Si, s)
        | Product (x::xs) as p ->
            printfn "6>product: x: {%s}" (x.ToString())
            let xs_product = elements_to_product xs
            let nonconvergence_detected = (List.exists (fun e -> e.ToString() = p.ToString()) l)
            printfn "         : xs: {%s}" (xs.ToString())
            //printfn "         : xs_product: {%s}" (xs_product.ToString())
            //printfn "         : nonconvergence_detected: {%b}" (nonconvergence_detected)
            //printfn "         : l.size: {%d}" (List.length l)
            if nonconvergence_detected then
                let orig = last l
                let ratio = orig / p
                //printfn "         : orig: {%s}" (orig.ToString())
                //printfn "         : ratio: {%s}" (ratio.ToString())
                match ratio with
                    | Number n -> 
                        printfn "Should Apply Linearity"
                        raise(ApplyLinearityRuleException ((Number n), zero, p))
                    | _ -> failwith "cannot converge (infinite recursion)"
            let ixs = antidifferentiate_rec s (p::l) xs_product
            let dx = differentiate s x
            let product = dx * xs_product
            //let ratio = (p) / (dx * ixs)
            //printfn "         : ixs: {%s}" (ixs.ToString())
            //printfn "         : dx: {%s}" (dx.ToString())
            //printfn "         : ratio: {%s}" (ratio.ToString())
            //printfn "         : p.toString(): {%s}" (p.ToString())
            //printfn "         : l: {%A}" (l)
            //printfn "         : nonconvergence_x: {%b}" (nonconvergence_x)
            //printfn "         : nonconvergence_xs: {%b}" (nonconvergence_xs)
            //printfn "         : product: {%s}" (product.ToString())

            try
                printfn "         : trying: %s - I(%s)" ((x*ixs).ToString()) ((dx*ixs).ToString())
                x * ixs - antidifferentiate_rec s (p::l) (dx * ixs)
            with
                | ApplyLinearityRuleException (n, e, t) when (t.ToString() = p.ToString()) ->
                    printfn ">> ApplyLinearityRuleException_last %s" (n.ToString())
                    printfn "         : l.size: {%d}" (List.length l)
                    printfn "         : n: {%s}" (n.ToString())
                    printfn "         : e: {%s}" (e.ToString())
                    printfn "         : resulting: %s" (((x * ixs - e) / (1+n)).ToString())
                    (x * ixs - e) / (1+n)
                | ApplyLinearityRuleException (n, e, t) when (List.length l > 0) ->
                    printfn ">> ApplyLinearityRuleException %s" (n.ToString())
                    printfn "         : l.size: {%d}" (List.length l)
                    printfn "         : n: {%s}" (n.ToString())
                    printfn "         : e: {%s}" (e.ToString())
                    printfn "         : resulting: %s" ((x * ixs).ToString())
                    raise(ApplyLinearityRuleException(n, x*ixs - e, t))
                    x * ixs
                | Failure msg -> 
                    printfn ">> <%s>" msg
                    match msg with
                        | _ -> 
                            printfn ">> Trying the other way"
                            antidifferentiate_rec s (p::l) (Product(xs_product :: x :: []))//(xs_product * x)
                //one
        | Product ([]) -> 
            printfn "7>product:"
            s
    
    [<CompiledName("Antidifferentiate")>]
    let antidifferentiate s x = (antidifferentiate_rec s [] x) + symbol "C"

    /// Antidifferentiate expression to symbol and substitute symbol with value
    [<CompiledName("AntidifferentiateAt")>]
    let antidifferentiateAt symbol value expression =
        expression |> antidifferentiate symbol |> Structure.substitute symbol value

    /// Taylor expansion of expression(symbol) at symbol=value of the first k terms
    [<CompiledName("Taylor")>]
    let taylor (k:int) symbol value expression =
        let rec impl n nf acc dxn =
            if n = k then acc else
            impl (n+1) (nf*(n+1)) (acc + (dxn |> Structure.substitute symbol value)/nf*(symbol-value)**n) (differentiate symbol dxn)
        impl 0 1 zero expression |> Algebraic.expand

    /// Find tangent line function for expression(symbol) at symbol=value
    [<CompiledName("TangentLine")>]
    let tangentLine symbol value expression =
        let slope = expression |> differentiate symbol |> Structure.substitute symbol value
        let intercept = expression |> Structure.substitute symbol value
        slope*(symbol - value) + intercept |> Algebraic.expand

    /// Find normal line (perpendicular to tangent) function for expression(symbol) at symbol=value
    [<CompiledName("NormalLine")>]
    let normalLine symbol value expression =
        let slope = expression |> differentiate symbol |> Structure.substitute symbol value
        let intercept = expression |> Structure.substitute symbol value
        -(1/slope)*(symbol - value) + intercept |> Algebraic.expand
