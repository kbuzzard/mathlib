# Type class inference -- tips and tricks

The type class inference system is a very neat system if (a) you know how to use
it properly and (b) it's appropriate to the situation you're trying to model.
If you are developing a new theory of `foo`s, and you decide
to let the type class inference system take care of figuring out exactly
which objects are `foo`s, then in all your lemmas you will be able
to write your `foo`s in square brackets, like
```
lemma eq_of_bar_eq {X Y: Type u} [foo X] [foo Y] : X.bar = Y.bar -> X = Y
```

and you will then be able to invoke such lemmas without having to clutter
up your file with proofs that various things are `foo`s. You will have
nifty instances like

```lean
instance topological_space_is_foo {X : Type u} [H : topological_space X] : foo X := { bar := ...}
```

and

```lean
instance product_of_foos {X Y : Type u} [foo X] [foo Y] : foo (X × Y) := { bar := ...}
```

and in theory you will barely have to mention that anything is a `foo`, you will construct a few to be getting along with and then let the type class inference system take care of everything else.

This document is a personal account of a few issues which you can run into in practice.

# "failed to synthesize type class instance" error #

This error occurs when the type class inference system can't infer what it has been asked to infer. To give a simple example, here's a lemma from core Lean:

```lean
theorem add_comm : ∀ {α : Type u} [_inst_1 : add_comm_semigroup α] (a b : α), a + b = b + a
```

If you have some type `X` and terms `a b : X`, and if `X` has an `+` (i.e. if we can construct a term of type `has_add X`) then it makes sense to ask if `a+b=b+a`. However we can only use lemma `add_comm` to prove this if someone supplies a term of type `add_comm_semigroup X`. Usually this would be the type class inference system, but if the type class inference system cannot do it for some reason, then writing `add_comm a b` to prove this will result in a "failed to synthesize type class instance" weeoe. You now have two problems: (1) constructing such a term `H : add_comm_semigroup X` yourself and (2) feeding it into `add_comm` somehow.

Let's assume you solved (1) and you have `H`. There are then several ways to solve (2).

Firstly, you could tell Lean that you're going to be supplying all the terms yourself and use `@add_comm`, writing `@add_comm X H a b` or `@add_comm _ H a b` instead of `add_comm a b`.

Secondly, you could tell the type class inference system about `H`. In term mode you might be able to write `attribute [instance] H` or changing `definition H := ...` to `instance H := ...`. In tactic mode you can instead write `letI := H`. Any of these methods should enable you to now write `add_comm a b`.

# Loops #

Often you want at most one coercion from one class to another, and if there are coercions from both `X` to `Y` and from `Y` to `X` then the coercion system can get into a loop resulting in timeouts. In particular if an end user wants to work with topological `foo`s having the trivial topology a lot, and decides to add an instance coercing a `foo` to a topological `foo`, then they might come unstuck if someone else has already put in a coercion from topological `foo`s back down to `foo`s by forgetting the topology.

# Diamonds #

These are a much worse problem. This is when the type class inference system manages to infer two different instances of a typeclass (for example `H1 : ring R` and `H2 : ring R` which are either different, or are equal but not definitionally equal. If they are actually different then this is evidence that you should not be using the type class inference system here -- the way classes work is that there is supposed to be one class per object; if you want more then you might want to consider using structures instead (although take a look at `topological_space.lean` to see type classes being used for topological spaces even in cases where more than one topology is being allowed).

If however your two instances are the same but this is a lemma rather than definitional equality, then you have probably found a diamond. These are not really supposed to happen, is my understanding of things. Here is an example from mathematics where an innocuous-looking set-up can result in a diamond.

Say we have two typeclasses `M` and `T` (for example `M` could be metric spaces and `T` topological spaces), and we have a coercion from things of type `M` to things of type `T` (for example we could consider the topological space associated to a metric space).

Now say both typeclasses also have products. In practice we would like the type class mechanism to know about this so we might write

```lean
instance M_has_products (\alpha \beta : Type) [M\alpha : M \alpha] [M\beta : M \beta] : M (\alpha \times \beta) := [insert construction of M structure on \alpha \times \beta from H\alpha and M\beta]

instance T_has_products (\alpha \beta : Type) [T\alpha : T \alpha] [T\beta : T \beta] : T (\alpha \times \beta) := [insert construction of T structure on \alpha \times \beta from T\alpha and T\beta]
```

For example, with metric spaces we could use the distance `d((a1,b1),(a2,b2))=sqrt(d(a1,b1)^2+d(a2,b2)^2)` to define a distance on the product, and with topological spaces we could just use the product topology. Of course at some point we are going to need the theorem that the topological space structure on the product of two metric spaces equals the structure given by the product of the underlying topological spaces, but of course this theorem is not too hard to prove.

However the proof of this theorem is extremely unlikely to be `rfl` and this is a problem for the type class inference system, as the _theorem_ apparently can not somehow be built into the system. What happens in practice is that given two types of class M, the type class inference system now knows two possible ways of putting a structure T structure on their product, and maybe sometimes it ends up choosing one way and some times the other way, resulting in the user having two topological spaces X and Y which look to the end user that they should be definitionally equal but which are not, the obstruction lying deep within some inferred structures. The result is situations where Lean cannot do something which looks completely obvious to the end user because some part of a structure is equal to, but not definitionally equal to, what the end user thinks. This results in frustrating errors like substitutions failing in situations where they should "clearly not" fail.

# A possible fix

Coercions are subtle. Often you want at most one coercion from one class to another, and if there are coercions from `X` to `Y` and from `Y` to `X` then the coercion system can get into a loop resulting in timeouts. Now if "every coercion between typeclasses was a forgetful functor" then this problem would go away, because any coercion would just be forgetting structure. So one way of fixing the diamond issue above, which sounds absurd to a mathematician but which really seems to happen in Lean, is that the moment you realise that you want to make Lean automatically realise that you want every metric space to automatically be a topological space, you put the topological space structure *as an explicit part of the metric space structure* but save the user from seeing this by inferring the extra structure internally.

[example here of M having extra fields, namely those of T, which are calculated automatically by the system. Maybe M could have two fields n : nat, and T could have one, namely their sum]




# To be tidied

Mario example:

```lean
class has_a_nat (α : Type) := (Z : ℕ)
class has_two_nats (α : Type) := (X Y : ℕ)
open has_a_nat has_two_nats

instance nat_of_two {α} [has_two_nats α] : has_a_nat α :=
{ Z := X α + Y α }

instance has_a_nat.prod {α β} [has_a_nat α] [has_a_nat β] : has_a_nat (α × β) :=
{ Z := Z α + Z β }

instance has_two_nats.prod {α β} [has_two_nats α] [has_two_nats β] : has_two_nats (α × β) :=
{ X := X α + X β,
  Y := Y α + Y β }

example {α β} [has_two_nats α] [has_two_nats β] :
  Z (α × β) = @Z (α × β) nat_of_two := rfl
/-
type mismatch, term
  @rfl.{?l_1} ?m_2 ?m_3
has type
  @eq.{?l_1} ?m_2 ?m_3 ?m_3
but is expected to have type
  @eq.{1} nat
    (@has_a_nat.Z (prod.{0 0} α β) (@has_a_nat.prod α β (@nat_of_two α _inst_1) (@nat_of_two β _inst_2)))
    (@has_a_nat.Z (prod.{0 0} α β) (@nat_of_two (prod.{0 0} α β) (@has_two_nats.prod α β _inst_1 _inst_2)))
-/
```

vs

```
class has_a_nat (α : Type) := (Z : ℕ)
class has_two_nats (α : Type) extends has_a_nat α :=
(X Y : ℕ)
(agree : Z = X + Y)
open has_a_nat has_two_nats

instance has_a_nat.prod {α β} [has_a_nat α] [has_a_nat β] : has_a_nat (α × β) :=
{ Z := Z α + Z β }

instance has_two_nats.prod {α β} [has_two_nats α] [has_two_nats β] : has_two_nats (α × β) :=
{ X := X α + X β,
  Y := Y α + Y β,
  agree := by simp [Z, agree] }

example {α β} [has_two_nats α] [has_two_nats β] :
  Z (α × β) = @Z (α × β) (has_two_nats.to_has_a_nat _) := rfl
```