In my last post, I remarked that the inverse bidirectional type system was obviously algorithmic. In this post, let's implement it! What follows is a bit of OCaml code implementing the type system of the previous post.

First, let's give a data type to represent the types of the linear type system. As usual, we will have a datatype `tp` with one constructor for each grammatical production. In the comment next to each constructor, I'll give the term that the constructor corresponds to.

``` ocaml
type tp = 
  | One                (* represents 1     *)
  | Tensor of tp * tp  (* represents A ⊗ B *) 
  | Lolli of tp * tp   (* represents A ⊸ B *) 
```

Now, we can give a datatype to represent expressions. We'll represent variables with strings, and use the datatype `exp` to represent expressions. As before, there is a comment connecting the datatype to the expressions of the grammar.

``` ocaml
type var = string

type exp = 
  | Unit                               (* represents ()                  *)
  | LetUnit of exp * exp               (* represents let () = e in e'    *)
  | Pair of exp * exp                  (* represents (e, e')             *)
  | LetPair of var * var * exp * exp   (* represents let (x,y) = e in e' *)
  | Lam of var * exp                   (* represents λx. e               *)
  | App of exp * exp                   (* represents e e'                *)
  | Var of var                         (* represents x                   *)
```

Now we have to do something annoying, and implement some functions on the option datatype which really should be in the standard library. Basically we just want the standard functional programming structure on option types -- folds, maps, and monadic structure -- so we just go ahead an implement it.

``` ocaml
module Option = struct
  type 'a t = 'a option

  let map f = function
    | None -> None
    | Some x -> Some (f x)


  let return x = Some x 

  let fail = None

  let (>>=) m f = 
    match m with
    | None -> None
    | Some x -> f x

   let fold some none = function
     | None -> none
     | Some x -> some x  
end
```

Now, we can actually implement the bidirectional typechecker. To understand the implementation, it's actually helpful to understand the interface, first.

``` ocaml
module type TYPING =  sig
  type ctx = (var * tp option) list
  type 'a t = ctx -> ('a * ctx) option 

  val map : ('a -> 'b) -> 'a t -> 'b t 
  val return : 'a -> 'b -> ('a * 'b) option
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  val synth : exp -> tp t
  val check : exp -> tp -> unit t
```

The basic structure of our typechecker is to give a pair of operations `check` and `synth`, which respectively check that an expression `e` has a type `tp`, and infer a type for an expression. This function will be written in a monadic style, so we also have a type constructor `'a t` for typechecking computations, and the usual assortment of functorial (`map`) and monadic (`return` and `>>=`) structure for this type.

The monadic type constructor `'a t` is a pretty basic state-and-exception monad. It plumbs the context (of type `ctx`) through the computation, and can either return a value and an updated context, or it will fail.

An interesting feature of this context representation is that it does not map variables to types – it maps them to the option type `tp option`. This is because of the way that the moding will work out; the type is an *output* of the typing relation, and so when we put a variable into the context, we will not give it a type, and use the computation to ascribe it a type, which will be reflected in the output context. This is also why we use a full state monad rather than a reader monad for the context – we are basically implementing part of Prolog's substitution threading here.

We will also need a number of operations to implement the typechecker.

``` ocaml
  val fail : 'a t
  val checkvar : var -> tp -> unit t
  val lookup : var -> tp t 
  val withvar : var -> 'a t -> 'a t
  val tp_eq : tp -> tp -> unit t
end
```

We will need to `fail` in order to judge programs ill-typed. The `checkvar x tp` operation gives the variable `x` the type `tp`. The `lookup x` operation will look in the context to find a a type for `x`, failing if `x` has not yet been given a type. The operation `withvar x m` will run the monadic computation `m` in a context extended with the variable `x`. (No type is given for the variable, because it's the job of `m` to give the variable a type.) Finall, there's an equality test `tp_eq tp1 tp2`, that acts as a guard, failing if the two arguments are unequal.

Now, we can move on to the actual implementation.

``` ocaml
module Typing : TYPING = struct
  type ctx = (var * tp option) list 

  type 'a t = ctx -> ('a * ctx) option 

  let map f m ctx = 
    let open Option in 
    m ctx >>= fun (x, ctx) -> 
    return (f x, ctx)

  let return x = fun ctx -> Some(x, ctx)

  let (>>=) m f = fun ctx -> 
    let open Option in 
    m ctx >>= fun (a, ctx') -> 
    f a ctx'
```

As promised, the computation type is a state-and-exception monad, and the implementation of `map` and the monadic unit and bind are pretty unsurprising. More interesting are the implementations of the actual operations in the monadic interface.

``` ocaml
  let fail : 'a t = fun ctx -> None 
```

Failure is easy to implement – it just ignores the context, and then returns `None`.

``` ocaml
  let rec checkvar (x : var) (tp : tp) : unit t = fun ctx -> 
    let open Option in 
    match ctx with
    | [] -> fail 
    | (y, None) :: rest when x = y -> return ((), (y, Some tp) :: rest)
    | (y, Some _) :: rest when x = y -> fail 
    | h :: rest -> checkvar x tp rest >>= fun ((), rest') -> 
                   return ((), h :: rest')
```

The way that `checkvar x tp` works is that it iterates through the variables in the context, looking for the hypothesis which matches the variable `x`. When it finds it, it returns an updated context with the type of `x` set to `Some tp`. If the variable is already set, then that means that this is the second use of the variable, and so `checkvar` fails – this enforces the property that variables are used *at most* one time. If the variable isn't in the context, then `checkvar` also fails, because this is an out-of-scope variable reference. All other hypotheses are left unchanged.

``` ocaml
  let lookup x (ctx : ctx) = 
    match List.assoc_opt x ctx with
    | None -> Option.fail
    | Some None -> Option.fail
    | Some (Some tp) -> Option.return(tp, ctx)
```

The `lookup x` computation is even simpler – it returns `tp` if `(x, Some tp)` is in the context, and fails otherwise.

``` ocaml
  let withvar (type a) (x : var) (m : a t) : a t = fun ctx -> 
    let open Option in 
    m ((x, None) :: ctx) >>= function
    | (r, (y, Some _) :: ctx') when x = y -> return (r, ctx') 
    | (r, (y, None) :: ctx') when x = y -> fail 
    | _ -> assert false
```

The `withvar x m` operation extends the context with the variable `x`, and then runs `m` in the extended context.

An invariant our context representation maintains is that the output context has exactly the same variables in exactly the same order as the input context, and so we just pop off the first variable of the output context before returning, checking to make sure that the type of the variable has been set (i.e., `Some _`) to ensure that the variable was used *at least* one time. In conjunction with `checkvar` ensuring that the variable is used *at most* one time, this will ensure that each variable is used exactly one time.

If the first variable of the output context isn't `x`, or if the output context is empty, then our invariant is broken, and so we signal an assertion failure.

``` ocaml
  let tp_eq (tp1 : tp) (tp2 : tp) = if tp1 = tp2 then return () else fail 
```

The `type_eq tp1 tp2` function just turns a boolean test into a guard. Now, we can go through the synthesis and checking functions clause-by-clause:

``` ocaml
  let rec synth = function
    | Unit -> return One
```

We synthesize the unit type for the unit value.

``` ocaml
    | Pair(e1, e2) -> synth e1 >>= fun tp1 -> 
                      synth e2 >>= fun tp2 -> 
                      return (Tensor(tp1, tp2))
```

To synthesize a type for a pair, we synthesize types for each of the components, and then return their tensor product.

``` ocaml
    | Lam(x, e) -> synth e >>= fun ret_tp -> 
                   lookup x >>= fun arg_tp -> 
                   return (Lolli(arg_tp, ret_tp))
```

Functions are interesting, because we need to deal with variables, and evaluation order plays out in a neat way here. We infer a type `ret_tp` for the body `e`, and then we look up the type `tp_arg` that the body `e` ascribed to the variable `x`. This lets us give a type `Lolli(tp_arg, tp_ret)` for the whole function.

``` ocaml
    | LetUnit(e, e') -> check e One >>= fun () -> 
                        synth e'
```

To synthesize a type for unit elimination, we synthesize a type for the body, and check that the scrutinee has the unit type `One`.

``` ocaml
    | LetPair(x, y, e, e') -> 
       withvar y (withvar x (synth e' >>= fun res_tp -> 
                             lookup x >>= fun tp1 -> 
                             lookup y >>= fun tp2 -> 
                             check e (Tensor(tp1, tp2)) >>= fun () -> 
                             return res_tp))
```

To eliminate a pair, we introduce (using `withvar`) scopes for the variables `x` and `y`, and then:

1.  We synthesize a type `res_tp` for the continuation `e'`.
2.  Since `e'` used `x` and `y`, we can look up the types they were used at (binding the type of `x` to `tp1` and the type of `y` to `tp2`).
3.  Then, we check that the scrutinee `e` has the type `Tensor(tp1, tp2)`.
4.  Finally, we return the type `res_tp` for the type of the whole expression.

``` ocaml
    | App(_, _) -> fail 
    | Var _ -> fail 
```

Since applications and variable references are checking, not synthesizing, we `fail` if we see one of them in synthesizing position. If they are in checking position, we can use the `check` function to typecheck them:

``` ocaml
  and check (e : exp) (tp : tp) : unit t = 
    match e with 
    | Var x -> checkvar x tp 
```

The variable case simply uses `checkvar`.

``` ocaml
    | App(e1, e2) -> synth e2 >>= fun tp_arg -> 
                     check e1 (Lolli(tp_arg, tp))
```

To check an application `e1 e2` at a type `tp`, we first synthesize the argument type by inferring a type `tp_arg` for `e2`, and then we check that `e1` has the function type `Lolli(tp_arg, tp)`.

``` ocaml
    | e -> synth e >>= tp_eq tp
end
```

Finally, when we find a synthesizing term in checking position, we infer a type for it and then see if it is equal to what we expected.

This code is, at-best, lightly-tested, but I knocked together a [small Github repository](https://github.com/neel-krishnaswami/inverse-bidirectional-typechecking) with the code. Enjoy!
