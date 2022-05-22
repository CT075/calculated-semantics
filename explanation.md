# Computing correct typesystems

This approach is inspired by the one used by Pickard and Hutton in the ICFP
2021 paper ["Dependently Typed Compilers"](http://www.cs.nott.ac.uk/~pszgmh/well-typed.pdf).

For the sake of discussion, for the rest of this piece, consider the following
language:

```
data Exp : Set where
  valB : Bool -> Exp
  valN : Nat -> Exp
  add : Exp -> Exp -> Exp
  if : Exp -> Exp -> Exp -> Exp
```

(we cannot use the common trick of parameterizing expressions by their type, as
typecheckers are pointless if there are no ill-typed expressions)

## Methodology

The goal is to derive small-step dynamics in such a way as to respect progress
and preservation by construction. The preservation theorem states that
expressions have *the same* type after stepping, and as such is a more natural
target for equational reasoning than progress, which is an existence theorem.

That is, our goal is to, given a function `synth : Exp -> Maybe Type` defining
the typing rules for our language, define the function `step` (with a
to-be-defined type) such that, for all `e : Exp`,

```
synth e == synth (step e)
```

Unfortunately, as stated, this is not sufficient to prove either progress or
preservation.

Firstly, note that it is possible to write a reasonable-looking `step` function
such that an ill-typed program steps to a well-typed one. For example,

```
if True then True else 0
```

This expression clearly is ill-typed, yet the obvious stepping judgment steps
this to the value `True`, which is clearly well-typed.

To work around this, we can add an argument to `step` witnessing that the
expression to be stepped is well-typed, suggesting something along the lines of

```
step : (e : Exp) -> Welltyped e -> Exp
```

One candidate for the type `Welltyped e` is simply the type `exists (tau : Type)
. synth e == just tau`, but this is quite difficult to work with in practice.
Instead, we encode the language typing rules as an inductive datatype
`⊢_:_`, giving

```
step : (e : Exp) -> (⊢ e : tau) -> Exp
```

As Agda functions are required to be total, note that a function of this type
actually almost serves as a proof of the progress theorem!

The last missing piece is to handle another form of expression that does not
step, namely values. It is easy enough to encode into the type of `step` by
introducing partiality:

```
step : (e : Exp) -> (⊢ e : tau) -> Maybe Exp
```

However, this makes the type of the preservation theorem significantly
more unwieldy, as we now need to destruct the option in the type:

```
preservation : (e : Exp) -> (p : (⊢ e : tau)) ->
  case step e p
   of Just e' -> synth e == synth e'
    | Nothing -> T
```

Instead, I chose to parameterize the `Exp` type by whether or not it steps. An
expression `Exp True` may step if it is well-typed, whereas `Exp False` may not.

```
data Exp : Bool -> Set where
  valB : Bool -> Exp false
  add : Exp b1 -> Exp b2 -> Exp true
  -- etc
```

This gives the real final types of `step` and `preservation`:

```
step : (e : Exp true) -> (⊢ e : tau) -> exists (b:Bool).Exp b
preservation :
  (e : Exp true) -> (p : (⊢ e : tau)) -> (synth e == synth (step e p))
```

## Example

For brevity (the full proofs can be found in the `.agda` files, including
stepping annotations), we will only show the case for `add`, and omit the
various witnesses of type-safety necessary to make the proof go through in
Agda.

Given:
```
synth (add e1 e2) =
  case synth e1
   of Nothing | Just bool -> Nothing
    | Just nat -> case synth e2
                   of Nothing | Just bool -> Nothing
                    | Just nat -> Just nat
```

Then we want to define `step` such that

```
synth (step (add e1 e2)) == synth (add e1 e2)
```

We can do this by manipulating `synth (add e1 e2)` until we reach an expression
of the form `synth e'`, where `e'` is not equal to `add e1 e2`. Then:

```
   synth (add e1 e2)
== case synth e1 of ...  # Definition of [synth]
```

From here, we can case on whether `e1` can step. If it can, then we can invoke
the inductive hypothesis on `synth e1` and proceed as follows:

```
   ...
== case synth (step e1) of ...  # By inductive hypothesis
== synth (add (step e1) e2)
```

giving us one case of `step`. The case in which `e2` is able to step proceeds
likewise.

Note that, by choosing to first invoke the inductive hypothesis on `e2`, or on
both (when possible), we end up with different forms of the dynamics for this
language -- left-first, right-first, or parallel.

In the case that both `e1` and `e2` cannot step, they must be `val` nodes
containing natural numbers by a canonical forms lemma. This gives:

```
   synth (add (valN n1) (valN n2))
== case synth (valN n1) of ...
== Just nat                         # evaluate as much as possible
```

From here, we are nominally stuck. Sticking with the pattern of previous cases,
we will likely need to step "backwards" from `Just nat`, but in this case,
there are too many possibilities. To break free, we need some way of
restricting our search space. Here are a few ideas:

- Relevance: Every bound variable should be used at least once in at least one
    case
- Simplification: Expressions should get "simpler" -- at least one case of
    stepping a node `N` should eliminate that node.
- Locality: If a node `N` steps to another node `M`, the constituents of `M`
    should not be created "from thin air", but rather should be related to the
    children of `N`.

Putting these together, we come up with the following guesses:

- We cannot step to `valB`, because `synthtype (valB _)` cannot produce `Just nat`
- We cannot step to `add`, because that would not be simplifying the expression
- We cannot step to `if`, because `if` has three children to be populated by
    `e1` and `e2`.
- Therefore, we must step to `valN`. In order to use both `n1` and `n2` (neither
    of which were inspected by `synth`), then, the only solution is to choose
    some operator `(·) : Nat -> Nat -> Nat`, and produce `valN (n1 · n2)`.

As for the specific choice of which operator `(·)`, we must make a choice here,
just as we needed to make a choice of which of `e1` and `e2` stepped first
earlier. As the name suggests, we will choose `(+)` and complete the proof:

```
   ...
== Just nat
== synth (valN (n1 + n2))  # definition of [synth], backwards
```

## Reflection

I'm not particularly satisfied with my choice of the three principles used to
narrow `add (valN n1) (valN n2)` down to `valN (n1 + n2)`, particularly the
definition of "simplification" and its interaction with "locality". Initially,
I had attempted to impose some notion of term "size" and enforce that it gets
smaller, but I don't believe that it generalized well.

