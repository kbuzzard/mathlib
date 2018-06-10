.. _tactics:

How does the ``ring`` tactic work?
================================

This page is in two parts. The first part is an extremely brief introduction
to what tactics are and what they do. For a far fuller introduction,
see `Programming In Lean<https://leanprover.github.io/programming_in_lean/programming_in_lean.pdf>`_ . The second part is an attempt to document mathlib's `ring` tactic, or, more precisely, the file `tactic/ring.html<https://github.com/leanprover/mathlib/blob/master/tactic/ring.lean>`_ in mathlib (to be completely exacy: this document currently uses commit `d5c73c0b372d1181ca386e3264497e2c56077d93` of the file).

Part I : the bare minimum about monad mode
==========================================

Access to a working copy of Lean whilst reading would probably be helpful, if you're learning this stuff for the first time.


The `option` monad
------------------

``option`` is just an inductive type. It's defined like this, right in the heart of core lean (type ``#check option`` and right click on ``option`` to see yourself).


.. code-block:: lean

   inductive option (α : Type u)
   | none {} : option
   | some (val : α) : option

So if ``α`` is a type, then ``option α`` is another type which is basicall  ``α`` plus one extra element called ``none``. A better name for ``none`` as far as we are concerned would be ``failed``. If ``a : α`` then ``some a`` is the corresponding term of type ``option α``.

I won't go into a formal definition of what a monad is, but ``option`` is a monad, which means that it has some nice properties. For example, even though a function isn't a type, we can kind-of take ``option`` of a function. If ``f : α → β`` then there's an obvious map ``option α → option β`` sending ``some a`` to ``some (f a)`` and ``none`` to ``none``. Slightly more subtly, there's a map ``option α × option β → option (α × β)``, which, for example, sends ``(none,b)`` to ``none``. The idea is -- if something failed, then we've failed.

The `tactic` monad
------------------

``tactic`` is just ``option`` with some variables and stuff. Why ``option``? We've all seen tactics fail -- for example the squiggly red line you get under a ``rw`` when Lean can't find the thing it's supposed to be rewriting, is a tactic failing. Here's an extremely simplistic (and actually slightly incorrect) way to think about what a tactic is doing. The tactic is given a job to do, as an input, for example "here's this goal -- can you try to simplify it?", and then the output of the tactic should be a simplified goal. However what if the tactic can't do what it is told to do? There are many reasons this might happen. For example what if ``simp`` finds that the goal can't be simplified, or ``rw`` can't find any instances of the thing it is supposed to be rewriting? What if the tactic had a bug? (this can happen, we'll say more about this later and why we don't have to worry about Lean proving ``false`` because of a buggy tactic).

Because we want to let a tactic have the possibility of failing, the output of a tactic is not something like a term or a goal, it's going to be of the form ``option expr`` or something like this, where ``expr`` is an expression, and ``option`` gives it the chance to return "I failed".

I learnt a lot about Lean once I realised how easy it was to examine everything -- you just had to know where to look. The usual tactics which you use when writing in tactic mode are all in ``tactic.interactive``. So, for example, to see the type of the underlying function that is run when you type ``simp`` in tactic mode, you can type


.. code-block:: lean

   #check tactic.interactive.simp

and similarly for other tactics like ``rw`` and ``unfold`` and so on. Of course it mostly looks like gobble-de-gook if you don't know anything about tactics, but note that the output will almost certainly be of the form ``tactic unit``. As you might well know, ``unit`` is an inductive type with just one term, ``unit.star``. So where are all the goals and things which the tactic just changed? They're all stored as variables within the tactic monad, using tricks explained in section 7.3 of `Programming In Lean<https://leanprover.github.io/programming_in_lean/programming_in_lean.pdf>`_ .

Writing a tactic
----------------

There are examples in `Programming In Lean<https://leanprover.github.io/programming_in_lean/programming_in_lean.pdf>`_ . But I just want to briefly introduce "monad mode", which you enter with the command ``do``. Just as ``by`` or ``begin .. end`` put you into tactic mode and ``calc`` puts you into calc mode (I think these modes are called "environments"), ``do`` puts you into monad mode, where you have access to a bunch of variables such as the goal and hypotheses -- this is where they're stored.

One very funny thing about tactic mode is that we are allowed to fail, so we can write code which looks much more like procedural code. The problem is that things get a bit more complicated. Everything is a ``tactic`` this or ``tactic`` that, pretty much all functions return ``tactic something`` but you also sometimes want access to normal functions, and the notation used to informally switch between the tactic and non-tactic objects looks a bit scary at first:

.. code-block:: lean

   meta def mk_cache (e : expr) : tactic cache :=
   do α ← infer_type e,
      c ← mk_app ``comm_semiring [α] >>= mk_instance,
      u ← mk_meta_univ,
      infer_type α >>= unify (expr.sort (level.succ u)),
      u ← get_univ_assignment u,
      return ⟨α, u, c⟩

This code block is from very early on in ``tactic/ring.lean`` and the first goal of this document is to convince people that this code is actually really easy to *read*. I am not suggesting that people will be writing their own tactics at the end of this, but I am suggesting that actually reading tactic code might not be impossible, especially if one does it within Lean (thus gaining the ability to hover over or click on functions and see their type, definition and so on).

I want to end Part 1 as quickly as possible so we can get to this code in Part IIand take a look at it. But one important thing I want to mention before we do is that ultimately a Lean tactic is more than just an algoriothm which solves a task. For example a tactic which sorts a list of nats is more than a python program which sorts a list of nats -- the Lean tactic has to both sort the list, and then, for the output to be useful, it has to return proofs that (a) the new list is some re-arranged version of the old list and (b) the new list is in order. To give another example -- ``simp`` does not just produce a new goal from an old one via some hack -- it has to also prove that if we can prove our new goal then we can deduce the old one. The Lean tactic has to be both an algorithm, *and* a proof that the algorithm works. This is why writing Lean tactics is harder than writing python code.

Is it the case that one can separate the algorithm and the proof into two different problems? I don't really know yet, but probably if I keep reading ``tactic/ring.lean`` I might begin to get an inkling. So let's end part 1 here and go straight into the ``tactic/ring.lean`` code and see if we can make some sense of the first 30 lines of it.

Part II : ``tactic/ring.lean``
==============================

Let me just try and read this code from top to bottom.

.. code-block:: lean
   /-
   Copyright (c) 2018 Mario Carneiro. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Mario Carneiro
   
   Evaluate expressions in the language of (semi-)rings.
   Based on http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf .
   -/
   import algebra.group_power tactic.norm_num
   
   universes u v w
   open tactic
   
   def horner {α} [comm_semiring α] (a x : α) (n : ℕ) (b : α) := a * x ^ n + b

Note that the type of ``α`` is being inferred by type class inference here (using ``comm_semiring`` I guess). Rather than focussing on this ``horner`` definition, let me mention here that if ``horner`` is ever used then Lean might find itself having to cook up ``α : Type u`` for some universe ``u`` (which the unifier (I think) will try to do, using the types of the inputs ``a, x, b``), and ``H : comm_semiring α``, which it would try and do using typeclass inference.

   namespace tactic
   namespace ring
   
   meta structure cache :=
   (α : expr)
   (univ : level)
   (comm_semiring_inst : expr)

Here's the first hint that we are dealing with tactics here. The structure ``tactic.ring.cache`` (which you can inspect in Lean if you ``import tactic.ring``) looks like a normal structure, but it using types which we may have never heard of. If you remove the ``meta`` you'll see why -- the types ``expr`` and ``level`` are "untrusted". Untrusted code has access to goals and might even be able to just change them randomly -- is this right? These untrusted types -- ``level`` is supposed to represent a universe level, and ``expr`` is a general Lean expression like ``2`` or ``2+2=4`` or ``ℕ`` -- there are ``expr`` versions of all of these things.

Note that evem though ``α`` and ``comm_semiring_inst`` both have type ``expr`` one can't help but wonder whether one of them will represent the ``α`` in ``horner`` and the other will represent the proof that ``α`` is a commutative semiring. Note that there is no typeclass checking here -- everything is an ``expr``.
   
   meta def mk_cache (e : expr) : tactic cache :=
   do α ← infer_type e,
      c ← mk_app ``comm_semiring [α] >>= mk_instance,
      u ← mk_meta_univ,
      infer_type α >>= unify (expr.sort (level.succ u)),
      u ← get_univ_assignment u,
      return ⟨α, u, c⟩

OK so this definition is ``meta`` because it mentions the ``tactic`` type, which is untrusted (and because it's full of ``expr``s). But it's not hard to figure out what this code must be doing. We go into monad mode with ``do`` and now we find ourselves writing procedural code in funny notation, with arrows instead of ``:=`` or ``=``. So ``e`` has type ``expr`` so it represents some Lean term, and this term should have a type. The first line after the ``do`` lets ``α`` be the type of ``e``. This looks different to how we talk about types in normal mode, but it's because ``e`` is an ``expr`` which is a pretty primtive object, and there are specialised functions doing basic things with ``expr``s with exotic names like ``infer_type``. These fancy functions are in core lean and many if not all of them are documented -- if you hover over ``infer_type`` then you see it sends ``expr`` to ``tactic expr`` and brief docs. If you want a bit of a shock then right-clock on infer_type and look at its definition.

The fact that ``infer_type`` is returning a ``tactic expr`` and not an ``expr`` is why we have to use the arrow -- we think of ``α`` but really it's ``some α`` (or ``return α``, as the tactic monad calls it).

After our definition of ``α`` we have a definition of ``c``, which seems to ask the type class inference system for an instance of ``comm_semiring α`` and then lets ``c`` be the answer. Note that this could fail, in which case our definition is just going to return ``none`` and possibly set some variable equal to a helpful error message explaining why we failed. The reason ``comm_semiring`` is taking a list rather than just  ``α`` is because we are borrowing it from term mode within monad mode, and when we lift it in with those two backticks it wants to take just one input, namely a list of all the inputs which it would have had in term mode. In term mode one can write ``_`` -- in monad mode one just uses ``none`` as the corresponding entry in the list.

We then define ``u`` to be a new universe, and then we seem to be making sure that the type of ``α`` is ``Sort (u+1)``. This messes with ``u`` a bit so we then redefine ``u`` to be the universe it now wants to be (note: we just defined ``u`` twice here -- this is normal in python but not possible in functional programming -- but there is something clever going on in monad mode here that lets us do it).

Once we have ``⟨α, u, c⟩`` set up to our satisfaction, we then create our instance of ``tactic.ring.cache`` a.k.a. ``cache``, and return it via the ``return`` command, which ensures it ends up as type ``tactic cache``.

   
   meta def cache.cs_app (c : cache) (n : name) : list expr → expr :=
   (@expr.const tt n [c.univ] c.α c.comm_semiring_inst).mk_app
   
   meta inductive destruct_ty : Type
   | const : ℚ → destruct_ty
   | xadd : expr → expr → expr → ℕ → expr → destruct_ty
   open destruct_ty
   
   meta def destruct (e : expr) : option destruct_ty :=
   match expr.to_rat e with
   | some n := some $ const n
   | none := match e with
     | `(horner %%a %%x %%n %%b) :=
       do n' ← expr.to_nat n,
          some (xadd a x n n' b)
     | _ := none
     end
   end
   
   meta def normal_form_to_string : expr → string
   | e := match destruct e with
     | some (const n) := to_string n
     | some (xadd a x _ n b) :=
       "(" ++ normal_form_to_string a ++ ") * (" ++ to_string x ++ ")^"
           ++ to_string n ++ " + " ++ normal_form_to_string b
     | none := to_string e
     end
   
   theorem zero_horner {α} [comm_semiring α] (x n b) :
     @horner α _ 0 x n b = b :=
   by simp [horner]
   
   theorem horner_horner {α} [comm_semiring α] (a₁ x n₁ n₂ b n')
     (h : n₁ + n₂ = n') :
     @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
   by simp [h.symm, horner, pow_add, mul_assoc]
   
   meta def refl_conv (e : expr) : tactic (expr × expr) :=
   do p ← mk_eq_refl e, return (e, p)
   
   meta def trans_conv (t₁ t₂ : expr → tactic (expr × expr)) (e : expr) :
     tactic (expr × expr) :=
   (do (e₁, p₁) ← t₁ e,
     (do (e₂, p₂) ← t₂ e₁,
       p ← mk_eq_trans p₁ p₂, return (e₂, p)) <|>
     return (e₁, p₁)) <|> t₂ e
   
   meta def eval_horner (c : cache) (a x n b : expr) : tactic (expr × expr) :=
   do d ← destruct a, match d with
   | const q := if q = 0 then
       return (b, c.cs_app ``zero_horner [x, n, b])
     else refl_conv $ c.cs_app ``horner [a, x, n, b]
   | xadd a₁ x₁ n₁ _ b₁ :=
     if x₁ = x ∧ b₁.to_nat = some 0 then do
       (n', h) ← mk_app ``has_add.add [n₁, n] >>= norm_num,
       return (c.cs_app ``horner [a₁, x, n', b],
         c.cs_app ``horner_horner [a₁, x, n₁, n, b, n', h])
     else refl_conv $ c.cs_app ``horner [a, x, n, b]
   end
   
   theorem const_add_horner {α} [comm_semiring α] (k a x n b b') (h : k + b = b'   ) :
     k + @horner α _ a x n b = horner a x n b' :=
   by simp [h.symm, horner]
   
   theorem horner_add_const {α} [comm_semiring α] (a x n b k b') (h : b + k = b'   ) :
     @horner α _ a x n b + k = horner a x n b' :=
   by simp [h.symm, horner]
   
   theorem horner_add_horner_lt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k b')
     (h₁ : n₁ + k = n₂) (h₂ : b₁ + b₂ = b') :
     @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner (horner a₂ x k a₁) x n₁    b' :=
   by simp [h₂.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]
   
   theorem horner_add_horner_gt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k b')
     (h₁ : n₂ + k = n₁) (h₂ : b₁ + b₂ = b') :
     @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner (horner a₁ x k a₂) x n₂    b' :=
   by simp [h₂.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]
   
   theorem horner_add_horner_eq {α} [comm_semiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
     (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
     @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
   by simp [h₃.symm, h₂.symm, h₁.symm, horner, add_mul, mul_comm]
   
   meta def eval_add (c : cache) : expr → expr → tactic (expr × expr)
   | e₁ e₂ := do d₁ ← destruct e₁, d₂ ← destruct e₂,
   match d₁, d₂ with
   | const n₁, const n₂ :=
     mk_app ``has_add.add [e₁, e₂] >>= norm_num
   | const k, xadd a x n _ b :=
     if k = 0 then do
       p ← mk_app ``zero_add [e₂],
       return (e₂, p) else do
     (b', h) ← eval_add e₁ b,
     return (c.cs_app ``horner [a, x, n, b'],
       c.cs_app ``const_add_horner [e₁, a, x, n, b, b', h])
   | xadd a x n _ b, const k :=
     if k = 0 then do
       p ← mk_app ``add_zero [e₁],
       return (e₁, p) else do
     (b', h) ← eval_add b e₂,
     return (c.cs_app ``horner [a, x, n, b'],
       c.cs_app ``horner_add_const [a, x, n, b, e₂, b', h])
   | xadd a₁ x₁ en₁ n₁ b₁, xadd a₂ x₂ en₂ n₂ b₂ :=
     if expr.lex_lt x₁ x₂ then do
       (b', h) ← eval_add b₁ e₂,
       return (c.cs_app ``horner [a₁, x₁, en₁, b'],
         c.cs_app ``horner_add_const [a₁, x₁, en₁, b₁, e₂, b', h])
     else if x₁ ≠ x₂ then do
       (b', h) ← eval_add e₁ b₂,
       return (c.cs_app ``horner [a₂, x₂, en₂, b'],
         c.cs_app ``const_add_horner [e₁, a₂, x₂, en₂, b₂, b', h])
     else if n₁ < n₂ then do
       k ← expr.of_nat (expr.const `nat []) (n₂ - n₁),
       (_, h₁) ← mk_app ``has_add.add [en₁, k] >>= norm_num,
       (b', h₂) ← eval_add b₁ b₂,
       return (c.cs_app ``horner [c.cs_app ``horner [a₂, x₁, k, a₁], x₁, en₁, b'   ],
         c.cs_app ``horner_add_horner_lt [a₁, x₁, en₁, b₁, a₂, en₂, b₂, k, b', h   ₁, h₂])
     else if n₁ ≠ n₂ then do
       k ← expr.of_nat (expr.const `nat []) (n₁ - n₂),
       (_, h₁) ← mk_app ``has_add.add [en₂, k] >>= norm_num,
       (b', h₂) ← eval_add b₁ b₂,
       return (c.cs_app ``horner [c.cs_app ``horner [a₁, x₁, k, a₂], x₁, en₂, b'   ],
         c.cs_app ``horner_add_horner_gt [a₁, x₁, en₁, b₁, a₂, en₂, b₂, k, b', h   ₁, h₂])
     else do
       (a', h₁) ← eval_add a₁ a₂,
       (b', h₂) ← eval_add b₁ b₂,
       (t, h₃) ← eval_horner c a' x₁ en₁ b',
       return (t, c.cs_app ``horner_add_horner_eq
         [a₁, x₁, en₁, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])
   end
   
   theorem horner_neg {α} [comm_ring α] (a x n b a' b')
     (h₁ : -a = a') (h₂ : -b = b') :
     -@horner α _ a x n b = horner a' x n b' :=
   by simp [h₂.symm, h₁.symm, horner]
   
   meta def eval_neg (c : cache) : expr → tactic (expr × expr) | e :=
   do d ← destruct e, match d with
   | const _ :=
     mk_app ``has_neg.neg [e] >>= norm_num
   | xadd a x n _ b := do
     (a', h₁) ← eval_neg a,
     (b', h₂) ← eval_neg b,
     p ← mk_app ``horner_neg [a, x, n, b, a', b', h₁, h₂],
     return (c.cs_app ``horner [a', x, n, b'], p)
   end
   
   theorem horner_const_mul {α} [comm_semiring α] (c a x n b a' b')
     (h₁ : c * a = a') (h₂ : c * b = b') :
     c * @horner α _ a x n b = horner a' x n b' :=
   by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]
   
   theorem horner_mul_const {α} [comm_semiring α] (a x n b c a' b')
     (h₁ : a * c = a') (h₂ : b * c = b') :
     @horner α _ a x n b * c = horner a' x n b' :=
   by simp [h₂.symm, h₁.symm, horner, add_mul, mul_right_comm]
   
   meta def eval_const_mul (c : cache) (k : expr) : expr → tactic (expr × expr)    | e :=
   do d ← destruct e, match d with
   | const _ :=
     mk_app ``has_mul.mul [k, e] >>= norm_num
   | xadd a x n _ b := do
     (a', h₁) ← eval_const_mul a,
     (b', h₂) ← eval_const_mul b,
     return (c.cs_app ``horner [a', x, n, b'],
       c.cs_app ``horner_const_mul [k, a, x, n, b, a', b', h₁, h₂])
   end
   
   theorem horner_mul_horner_zero {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ aa t)
     (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
     (h₂ : horner aa x n₂ 0 = t) :
     horner a₁ x n₁ b₁ * horner a₂ x n₂ 0 = t :=
   by rw [← h₂, ← h₁];
      simp [horner, mul_add, mul_comm, mul_left_comm, mul_assoc]
   
   theorem horner_mul_horner {α} [comm_semiring α]
     (a₁ x n₁ b₁ a₂ n₂ b₂ aa haa ab bb t)
     (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
     (h₂ : horner aa x n₂ 0 = haa)
     (h₃ : a₁ * b₂ = ab) (h₄ : b₁ * b₂ = bb)
     (H : haa + horner ab x n₁ bb = t) :
     horner a₁ x n₁ b₁ * horner a₂ x n₂ b₂ = t :=
   by rw [← H, ← h₂, ← h₁, ← h₃, ← h₄];
      simp [horner, mul_add, mul_comm, mul_left_comm, mul_assoc]
   
   meta def eval_mul (c : cache) : expr → expr → tactic (expr × expr)
   | e₁ e₂ := do d₁ ← destruct e₁, d₂ ← destruct e₂,
   match d₁, d₂ with
   | const n₁, const n₂ :=
     mk_app ``has_mul.mul [e₁, e₂] >>= norm_num
   | const n₁, _ :=
     if n₁ = 0 then do
       α0 ← expr.of_nat c.α 0,
       p ← mk_app ``zero_mul [e₂],
       return (α0, p) else
     if n₁ = 1 then do
       p ← mk_app ``one_mul [e₂],
       return (e₂, p) else
     eval_const_mul c e₁ e₂
   | _, const _ := do
     p₁ ← mk_app ``mul_comm [e₁, e₂],
     (e', p₂) ← eval_mul e₂ e₁,
     p ← mk_eq_trans p₁ p₂, return (e', p)
   | xadd a₁ x₁ en₁ n₁ b₁, xadd a₂ x₂ en₂ n₂ b₂ :=
     if expr.lex_lt x₁ x₂ then do
       (a', h₁) ← eval_mul a₁ e₂,
       (b', h₂) ← eval_mul b₁ e₂,
       return (c.cs_app ``horner [a', x₁, en₁, b'],
         c.cs_app ``horner_mul_const [a₁, x₁, en₁, b₁, e₂, a', b', h₁, h₂])
     else if x₁ ≠ x₂ then do
       (a', h₁) ← eval_mul e₁ a₂,
       (b', h₂) ← eval_mul e₁ b₂,
       return (c.cs_app ``horner [a', x₂, en₂, b'],
         c.cs_app ``horner_const_mul [e₁, a₂, x₂, en₂, b₂, a', b', h₁, h₂])
     else do
       (aa, h₁) ← eval_mul e₁ a₂,
       α0 ← expr.of_nat c.α 0,
       (haa, h₂) ← eval_horner c aa x₁ en₂ α0,
       if b₂.to_nat = some 0 then do
         return (haa, c.cs_app ``horner_mul_horner_zero
           [a₁, x₁, en₁, b₁, a₂, en₂, aa, haa, h₁, h₂])
       else do
         (ab, h₃) ← eval_mul a₁ b₂,
         (bb, h₄) ← eval_mul b₁ b₂,
         (t, H) ← eval_add c haa (c.cs_app ``horner [ab, x₁, en₁, bb]),
         return (t, c.cs_app ``horner_mul_horner
           [a₁, x₁, en₁, b₁, a₂, en₂, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H]   )
   end
   
   theorem horner_pow {α} [comm_semiring α] (a x n m n' a')
     (h₁ : n * m = n') (h₂ : a ^ m = a') :
     @horner α _ a x n 0 ^ m = horner a' x n' 0 :=
   by simp [h₁.symm, h₂.symm, horner, mul_pow, pow_mul]
   
   meta def eval_pow (c : cache) : expr → nat → tactic (expr × expr)
   | e 0 := do
     α1 ← expr.of_nat c.α 1,
     p ← mk_app ``pow_zero [e],
     return (α1, p)
   | e 1 := do
     p ← mk_app ``pow_one [e],
     return (e, p)
   | e m := do d ← destruct e,
     let N : expr := expr.const `nat [],
     match d with
     | const _ := do
       e₂ ← expr.of_nat N m,
       mk_app ``monoid.pow [e, e₂] >>= norm_num.derive
     | xadd a x n _ b := match b.to_nat with
       | some 0 := do
         e₂ ← expr.of_nat N m,
         (n', h₁) ← mk_app ``has_mul.mul [n, e₂] >>= norm_num,
         (a', h₂) ← eval_pow a m,
         α0 ← expr.of_nat c.α 0,
         return (c.cs_app ``horner [a', x, n', α0],
           c.cs_app ``horner_pow [a, x, n, e₂, n', a', h₁, h₂])
       | _ := do
         e₂ ← expr.of_nat N (m-1),
         l ← mk_app ``monoid.pow [e, e₂],
         (tl, hl) ← eval_pow e (m-1),
         (t, p₂) ← eval_mul c tl e,
         hr ← mk_eq_refl e,
         p₂ ← mk_app ``norm_num.subst_into_prod [l, e, tl, e, t, hl, hr, p₂],
         p₁ ← mk_app ``pow_succ' [e, e₂],
         p ← mk_eq_trans p₁ p₂,
         return (t, p)
       end
     end
   
   theorem horner_atom {α} [comm_semiring α] (x : α) : x = horner 1 x 1 0 :=
   by simp [horner]
   
   lemma subst_into_neg {α} [has_neg α] (a ta t : α) (pra : a = ta) (prt : -ta =    t) : -a = t :=
   by simp [pra, prt]
   
   meta def eval_atom (c : cache) (e : expr) : tactic (expr × expr) :=
   do α0 ← expr.of_nat c.α 0,
      α1 ← expr.of_nat c.α 1,
      n1 ← expr.of_nat (expr.const `nat []) 1,
      return (c.cs_app ``horner [α1, e, n1, α0], c.cs_app ``horner_atom [e])
   
   lemma subst_into_pow {α} [monoid α] (l r tl tr t)
     (prl : (l : α) = tl) (prr : (r : ℕ) = tr) (prt : tl ^ tr = t) : l ^ r = t    :=
   by simp [prl, prr, prt]
   
   meta def eval (c : cache) : expr → tactic (expr × expr)
   | `(%%e₁ + %%e₂) := do
     (e₁', p₁) ← eval e₁,
     (e₂', p₂) ← eval e₂,
     (e', p') ← eval_add c e₁' e₂',
     p ← mk_app ``norm_num.subst_into_sum [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
     return (e', p)
   | `(%%e₁ - %%e₂) := do
     e₂' ← mk_app ``has_neg.neg [e₂],
     mk_app ``has_add.add [e₁, e₂'] >>= eval
   | `(- %%e) := do
     (e₁, p₁) ← eval e,
     (e₂, p₂) ← eval_neg c e₁,
     p ← mk_app ``subst_into_neg [e, e₁, e₂, p₁, p₂],
     return (e₂, p)
   | `(%%e₁ * %%e₂) := do
     (e₁', p₁) ← eval e₁,
     (e₂', p₂) ← eval e₂,
     (e', p') ← eval_mul c e₁' e₂',
     p ← mk_app ``norm_num.subst_into_prod [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
     return (e', p)
   | e@`(has_inv.inv %%_) := (do
       (e', p) ← norm_num.derive e,
       e'.to_rat,
       return (e', p)) <|> eval_atom c e
   | e@`(%%e₁ / %%e₂) := do
     e₂' ← mk_app ``has_inv.inv [e₂],
     mk_app ``has_mul.mul [e₁, e₂'] >>= eval
   | e@`(%%e₁ ^ %%e₂) := do
     (e₂', p₂) ← eval e₂,
     match e₂'.to_nat with
     | none := eval_atom c e
     | some k := do
       (e₁', p₁) ← eval e₁,
       (e', p') ← eval_pow c e₁' k,
       p ← mk_app ``subst_into_pow [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
       return (e', p)
     end
   | e := match e.to_nat with
     | some _ := refl_conv e
     | none := eval_atom c e
     end
   
   theorem horner_def' {α} [comm_semiring α] (a x n b) : @horner α _ a x n b = x    ^ n * a + b :=
   by simp [horner, mul_comm]
   
   theorem mul_assoc_rev {α} [semigroup α] (a b c : α) : a * (b * c) = a * b * c    :=
   by simp [mul_assoc]
   
   theorem pow_add_rev {α} [monoid α] (a b : α) (m n : ℕ) : a ^ m * a ^ n = a ^    (m + n) :=
   by simp [pow_add]
   
   theorem pow_add_rev_right {α} [monoid α] (a b : α) (m n : ℕ) : b * a ^ m * a    ^ n = b * a ^ (m + n) :=
   by simp [pow_add, mul_assoc]
   
   theorem add_neg_eq_sub {α : Type u} [add_group α] (a b : α) : a + -b = a - b    := rfl
   
   @[derive has_reflect]
   inductive normalize_mode | raw | SOP | horner
   
   meta def normalize (mode := normalize_mode.horner) (e : expr) : tactic (expr    × expr) := do
   pow_lemma ← simp_lemmas.mk.add_simp ``pow_one,
   let lemmas := match mode with
   | normalize_mode.SOP :=
     [``horner_def', ``add_zero, ``mul_one, ``mul_add, ``mul_sub,
      ``mul_assoc_rev, ``pow_add_rev, ``pow_add_rev_right,
      ``mul_neg_eq_neg_mul_symm, ``add_neg_eq_sub]
   | normalize_mode.horner :=
     [``horner.equations._eqn_1, ``add_zero, ``one_mul, ``pow_one,
      ``neg_mul_eq_neg_mul_symm, ``add_neg_eq_sub]
   | _ := []
   end,
   lemmas ← lemmas.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
   (_, e', pr) ← ext_simplify_core () {}
     simp_lemmas.mk (λ _, failed) (λ _ _ _ _ e, do
       c ← mk_cache e,
       (new_e, pr) ← match mode with
       | normalize_mode.raw := eval c
       | normalize_mode.horner := trans_conv (eval c) (simplify lemmas [])
       | normalize_mode.SOP :=
         trans_conv (eval c) $
         trans_conv (simplify lemmas []) $
         simp_bottom_up' (λ e, norm_num e <|> pow_lemma.rewrite e)
       end e,
       guard (¬ new_e =ₐ e),
       return ((), new_e, some pr, ff))
      (λ _ _ _ _ _, failed) `eq e,
   return (e', pr)
   
   end ring
   
   namespace interactive
   open interactive interactive.types lean.parser
   open tactic.ring
   
   local postfix `?`:9001 := optional
   
   /-- Tactic for solving equations in the language of rings.
     This version of `ring` fails if the target is not an equality
     that is provable by the axioms of commutative (semi)rings. -/
   meta def ring1 : tactic unit :=
   do `(%%e₁ = %%e₂) ← target,
     c ← mk_cache e₁,
     (e₁', p₁) ← eval c e₁,
     (e₂', p₂) ← eval c e₂,
     is_def_eq e₁' e₂',
     p ← mk_eq_symm p₂ >>= mk_eq_trans p₁,
     tactic.exact p
   
   meta def ring.mode : lean.parser ring.normalize_mode :=
   with_desc "(SOP|raw|horner)?" $
   do mode ← ident?, match mode with
   | none         := return ring.normalize_mode.horner
   | some `horner := return ring.normalize_mode.horner
   | some `SOP    := return ring.normalize_mode.SOP
   | some `raw    := return ring.normalize_mode.raw
   | _            := failed
   end
   
   /-- Tactic for solving equations in the language of rings.
     Attempts to prove the goal outright if there is no `at`
     specifier and the target is an equality, but if this
     fails it falls back to rewriting all ring expressions
     into a normal form. When writing a normal form,
     `ring SOP` will use sum-of-products form instead of horner form. -/
   meta def ring (SOP : parse ring.mode) (loc : parse location) : tactic unit :=
   match loc with
   | interactive.loc.ns [none] := ring1
   | _ := failed
   end <|>
   do ns ← loc.get_locals,
      tt ← tactic.replace_at (normalize SOP) ns loc.include_goal
         | fail "ring failed to simplify",
      when loc.include_goal $ try tactic.reflexivity
   
   end interactive
   end tactic
   
   -- TODO(Mario): fix
   -- example (x : ℤ) : x^3 + x^2 + x = x^3 + (x^2 + x) := by ring
   
   
   
***********************************************************   

EOF

   *****************************************
   
   Informally, a *proposition* is a true-false statement in Lean. Do not
   confusion a proposition with its proof.
   
   A proposition ``P`` is a Type, which lives in the :doc:`universe <definitions   /universes>` called ``Prop``.
   Because ``P`` is a type, it makes sense to talk about terms of type ``P``.
   A term of type ``P`` is called a proof of ``P``.
   
   In the Lean code below we define two propositions, and check that they
   are in the Prop universe.
   
   .. code-block:: lean
   
      definition P : Prop := 2 + 2 = 4
      definition Q : Prop := 2 + 2 = 5 
   
      #check P -- P : Prop
      #check Q -- Q : Prop
   
   It is impossible to construct a term of type ``Q`` -- this would be a proof o   f ``Q``. However we can construct a term of type ``P``:
   
   .. code-block:: lean
      definition P : Prop := 2 + 2 = 4
   
      definition HP : P :=
      begin
        refl -- lean magic
      end  
   
      #check (HP : P) 
      #check (P : Prop)
      
   
   
   
   The `intro` tactic can be used on a goal of the form ``X → Y``.
   It assumes `X` and changes the goal to `Y`. More formally, `intro x`
   introduces a new term `x : X` into the local context and changes the
   goal to ``Y``.
   
   A common usage case is when ``P`` and ``Q`` are :doc:`Propositions </definiti   on/proposition>`, and your goal is ``⊢ P → Q``
   
   See :doc:`/usage/restructuredtext/domains` for all the available domains
   and their directives/roles.
   The way of thinking about ``intro`` depends on whether you are talking
   about proofs or data. Here are two examples.
   
   .. code-block:: lean
   
       -- define the squaring function
       
       definition square : ℕ → ℕ :=
       begin -- goal currently ℕ → ℕ
         intro n, -- context now
                  /-
                  n : ℕ
                  ⊢ ℕ
                  -/
         exact n ^ 2,
       end 
       
       #eval square 5 -- 25
       
       theorem easy (P : Prop) : P → true := 
       begin
         intro hP,
         trivial,
       end 
       
       theorem trickier (P Q R : Prop) : (P → Q) ∧ (P → R) → (P → Q ∧ R) :=
       begin
         intro HPQPR,
         have HPQ : P → Q,
           exact HPQPR.left,
         have HPR : P → R,
           exact HPQPR.right,
         intro HP,
         split,
         { -- goal is Q
           exact HPQ HP
         },
         { -- goal is R
           exact HPR HP
         }
         end
         
          
   If ``P`` and ``Q`` are Propositions, and our goal is ``P → Q``, that is, to
   prove that ``P`` implies ``Q``, then ``intro hP`` will introduce
   a proof ``hP`` of ``P``, leaving us with the goal of proving ``Q``.
   Recall that in Lean, if ``P`` is in the ``Prop`` universe then it is a Type,
   and a proof of ``P`` is just a term of type ``P``.
       
       
       
       
       
   .. py:function:: intro x
                 foo(y, z)
   
   
   	      Is this any use to me?
   	      
       
   
       
          
   
   
   
   1) A *binary relation* :math:`\star` on a set :math:`S` is the following info   rmation: for each :math:`(s,t)\in S^2` we have a proposition :math:`s \star t   `. An example is the less-than relation :math:`<` on :math:`\mathbb{R}`; for    each pair of real numbers :math:`a` and :math:`b` we have a true-false statem   ent :math:`a<b`.
   
   2) Two other equivalent ways of modelling the definition: a binary relation c   an be thought of as a subset of :math:`S^2`, the dictionary being that :math:   `(s,t)` is in the subset iff :math:`s \star t`. Or it could be thought of as    a map from :math:`S^2` to the set :math:`\{T,F\}`.
   
   3) A binary relation :math:`\sim` on a set :math:`S` is *reflexive* if
   
   .. math::
         
      \forall s\in S, s\sim s,
   
   and it is *symmetric* if
   
   .. math::
   
      \forall s,t\in S, s \sim t \to t \sim s
   
   It is *transitive* if
   
   .. math::
   
      \forall s, t, u\in S, s \sim t \land t \sim u \to s \sim u,
   
   and it is an *equivalence relation* if it is reflexive, symmetric
   and transitive. Examples show that none of the three axioms for an
   equivalence relation can be dropped. For example the binary relation
   :math:`\le` is reflexive and transitive, but not symmetric.
   
   4) If :math:`\sim` is an equivalence relation on :math:`S`, we may partition    :math:`S` into disjoint *equivalence classes*; these form a *partition* of :m   ath:`S`. One can check that conversely, from a partition of :math:`S` one can    construct an equivalence relation, defined by :math:`s \sim t` if :math:`s`    and :math:`t` are in the same part of the partition, and these two dictionari   es provide two distinct ways of thinking about the same idea.
   
   .. todo:: I have no colours, I have no "try me" link and I have stuff visible    outside the BEGIN/END.
   
   Dependent type theory
   =====================
   
   Let's start by setting up a 
   
   .. code-block:: lean
   
       universe u
   
       def list.to_set {α : Type u} : list α → set α
       | []     := ∅
       | (h::t) := {h} ∪ list.to_set t
   
       instance list_to_set_coe (α : Type u) : 
         has_coe (list α) (set α) :=
       ⟨list.to_set⟩
   
       def s : set nat  := {1, 2}
   
       -- BEGIN
       #check s ∪ ↑[3, 2]
   
       variables n m : nat
       variable i : int
       #check i + ↑n + ↑m
       #check i + ↑(n + m)
       #check ↑n + i
       -- END
   
   
   Here is a test about documenting the intro tactic
   
   The :py:func:`intro` tactic can be used for...
   
   We have seen that Lean's elaborator provides helpful automation, filling in i   nformation that is tedious to enter by hand. In this section we will explore    a simple but powerful technical device known as *type class inference*, which    provides yet another mechanism for the elaborator to supply missing informat   ion.
   
   The notion of a *type class* originated with the *Haskell* programming langua   ge. In that context, it is often used to associate operations, like a canonic   al addition or multiplication operation, to a data type. Many of the original    uses carry over, but, as we will see, the realm of interactive theorem provi   ng raises even more possibilities for their use.
   
   Type Classes and Instances
   --------------------------
   
   Any family of types can be marked as a *type class*. We can then declare part   icular elements of a type class to be *instances*. These provide hints to the    elaborator: any time the elaborator is looking for an element of a type clas   s, it can consult a table of declared instances to find a suitable element.
   
   More precisely, there are three steps involved:
   
   -  First, we declare a family of inductive types to be a type class.
   -  Second, we declare instances of the type class.
   -  Finally, we mark some implicit arguments with square brackets instead of c   urly brackets, to inform the elaborator that these arguments should be inferr   ed by the type class mechanism.
   
   Let us start with a simple example. Many theorems hold under the additional a   ssumption that a type is inhabited, which is to say, it has at least one elem   ent. For example, if ``α`` is a type, ``∃ x : α, x = x`` is true only if ``α   `` is inhabited. Similarly, it often happens that we would like a definition    to return a default element in a "corner case." For example, we would like th   e expression ``head l`` to be of type ``α`` when ``l`` is of type ``list α``;    but then we are faced with the problem that ``head l`` needs to return an "a   rbitrary" element of ``α`` in the case where ``l`` is the empty list, ``nil``   .
   
   The standard library defines a type class ``inhabited : Type → Type`` to ena   ble type class inference to infer a "default" or "arbitrary" element of an in   habited type. In the example below, we use a namespace ``hidden`` as usual to    avoid conflicting with the definitions in the standard library.
   
   Let us start with the first step of the program above, declaring an appropria   te class:
   
   .. code-block:: lean
   
       namespace hidden
       -- BEGIN
       class inhabited (α : Type _) :=
       (default : α)
       -- END
       end hidden
   
   The command ``class`` above is shorthand for
   
   .. code-block:: lean
   
       namespace hidden
       -- BEGIN
       @[class] structure inhabited (α : Type _) :=
       (default : α)
       -- END
       end hidden
   
   An element of the class ``inhabited α`` is simply an expression of the form `   `inhabited.mk a``, for some element ``a : α``. The projection ``inhabited.def   ault`` will allow us to "extract" such an element of ``α`` from an element of    ``inhabited α``.
   
   The second step of the program is to populate the class with some instances:
   
.. code-block:: lean

    namespace hidden
    -- BEGIN
    instance Prop_inhabited : inhabited Prop :=
    inhabited.mk true

    instance bool_inhabited : inhabited bool :=
    inhabited.mk tt

    instance nat_inhabited : inhabited nat :=
    inhabited.mk 0

    instance unit_inhabited : inhabited unit :=
    inhabited.mk ()
    -- END
    end hidden

In the Lean standard library, we regularly use the anonymous constructor when defining instances. It is particularly useful when the class name is long.

.. code-block:: lean

    namespace hidden
    -- BEGIN
    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩
    -- END
    end hidden

These declarations simply record the definitions ``Prop_inhabited``, ``bool_inhabited``, ``nat_inhabited``, and ``unit_inhabited`` on a list of instances. Whenever the elaborator is looking for a value to assign to an argument ``?M`` of type ``inhabited α`` for some ``α``, it can check the list for a suitable instance. For example, if it looking for an instance of ``inhabited Prop``, it will find ``Prop_inhabited``.

The final step of the program is to define a function that infers an element ``s : inhabited α`` and puts it to good use. The following function simply extracts the corresponding element ``a : α``:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    def default (α : Type) [s : inhabited α] : α :=
    @inhabited.default α s
    -- END
    end hidden

This has the effect that given a type expression ``α``, whenever we write ``default α``, we are really writing ``default α ?s``, leaving the elaborator to find a suitable value for the metavariable ``?s``. When the elaborator succeeds in finding such a value, it has effectively produced an element of type ``α``, as though by magic.

.. code-block:: lean

    #check default Prop  -- Prop
    #check default nat   -- ℕ
    #check default bool  -- bool
    #check default unit  -- unit

In general, whenever we write ``default α``, we are asking the elaborator to synthesize an element of type ``α``.

Notice that we can "see" the value that is synthesized with ``#reduce``:

.. code-block:: lean

    #reduce default Prop  -- true
    #reduce default nat   -- 0
    #reduce default bool  -- tt
    #reduce default unit  -- ()

Sometimes we want to think of the default element of a type as being an *arbitrary* element, whose specific value should not play a role in our proofs. For that purpose, we can write ``arbitrary α`` instead of ``default α``. The definition of ``arbitrary`` is the same as that of default, but is marked ``irreducible`` to discourage the elaborator from unfolding it. This does not preclude proofs from making use of the value, however, so the use of ``arbitrary`` rather than ``default`` functions primarily to signal intent.

Chaining Instances
------------------

If that were the extent of type class inference, it would not be all the impressive; it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table. What makes type class inference powerful is that one can *chain* instances. That is, an instance declaration can in turn depend on an implicit instance of a type class. This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

For example, the following definition shows that if two types ``α`` and ``β`` are inhabited, then so is their product:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    instance prod_inhabited 
        {α β : Type} [inhabited α] [inhabited β] : 
      inhabited (prod α β) :=
    ⟨(default α, default β)⟩
    -- END
    end hidden

With this added to the earlier instance declarations, type class instance can infer, for example, a default element of ``nat × bool × unit``:

.. code-block:: lean

    #check default (nat × bool)
    #reduce default (nat × bool)

Given the expression ``default (nat × bool)``, the elaborator is called on to infer an implicit argument ``?M : inhabited (nat × bool)``. The instance ``prod_inhabited`` reduces this to inferring ``?M1 : inhabited nat`` and ``?M2 : inhabited bool``. The first one is solved by the instance ``nat_inhabited``. The second uses ``bool_inhabited``.

Similarly, we can inhabit function spaces with suitable constant functions:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    instance inhabited_fun (α : Type) {β : Type} [inhabited β] : 
      inhabited (α → β) :=
    ⟨(λ a : α, default β)⟩

    #check default (nat → nat × bool)
    #reduce default (nat → nat × bool)
    -- END
    end hidden

In this case, type class inference finds the default element
``λ (a : nat), (0, tt)``.

As an exercise, try defining default instances for other types, such as sum types and the list type.

Inferring Notation
------------------

We now consider the application of type classes that motivates their use in functional programming languages like Haskell, namely, to overload notation in a principled way. In Lean, a symbol like ``+`` can be given entirely unrelated meanings, a phenomenon that is sometimes called "ad-hoc" overloading. Typically, however, we use the ``+`` symbol to denote a binary function from a type to itself, that is, a function of type ``α → α → α`` for some type ``α``. We can use type classes to infer an appropriate addition function for suitable types ``α``. We will see in the next section that this is especially useful for developing algebraic hierarchies of structures in a formal setting.

The standard library declares a type class ``has_add α`` as follows:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    universes u

    class has_add (α : Type u) :=
    (add : α → α → α)

    def add {α : Type u} [has_add α] : α → α → α := has_add.add

    notation a ` + ` b := add a b
    -- END
    end hidden

The class ``has_add α`` is supposed to be inhabited exactly when there is an appropriate addition function for ``α``. The ``add`` function is designed to find an instance of ``has_add α`` for the given type, ``α``, and apply the corresponding binary addition function. The notation ``a + b`` thus refers to the addition that is appropriate to the type of ``a`` and ``b``. We can then declare instances for ``nat``, and ``bool``:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    instance nat_has_add : has_add nat :=
    ⟨nat.add⟩

    instance bool_has_add : has_add bool :=
    ⟨bor⟩

    #check 2 + 2    -- nat
    #check tt + ff  -- bool
    -- END
    end hidden

As with ``inhabited``, the power of type class inference stems not only from the fact that the class enables the elaborator to look up appropriate instances, but also from the fact that it can chain instances to infer complex addition operations. For example, assuming that there are appropriate addition functions for types ``α`` and ``β``, we can define addition on ``α × β`` pointwise:

.. code-block:: lean

    namespace hidden
    universes u v
    -- BEGIN
    instance prod_has_add {α : Type u} {β : Type v} 
        [has_add α] [has_add β] : 
      has_add (α × β) :=
    ⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, ⟨a₁+a₂, b₁+b₂⟩⟩

    #check (1, 2) + (3, 4)    -- ℕ × ℕ
    #reduce  (1, 2) + (3, 4)  -- (4, 6)
    -- END
    end hidden

We can similarly define pointwise addition of functions:

.. code-block:: lean

    namespace hidden
    universes u v
    -- BEGIN
    instance fun_has_add {α : Type u} {β : Type v} [has_add β] : 
      has_add (α → β) :=
    ⟨λ f g x, f x + g x⟩

    #check (λ x : nat, 1) + (λ x, 2)   -- ℕ → ℕ
    #reduce (λ x : nat, 1) + (λ x, 2)    -- λ (x : ℕ), 3
    -- END
    end hidden

As an exercise, try defining instances of ``has_add`` for lists, and show that they work as expected.

Decidable Propositions
----------------------

Let us consider another example of a type class defined in the standard library, namely the type class of ``decidable`` propositions. Roughly speaking, an element of ``Prop`` is said to be decidable if we can decide whether it is true or false. The distinction is only useful in constructive mathematics; classically, every proposition is decidable. But if we use the classical principle, say, to define a function by cases, that function will not be computable. Algorithmically speaking, the ``decidable`` type class can be used to infer a procedure that effectively determines whether or not the proposition is true. As a result, the type class supports such computational definitions when they are possible while at the same time allowing a smooth transition to the use of classical definitions and classical reasoning.

In the standard library, ``decidable`` is defined formally as follows:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    class inductive decidable (p : Prop) : Type
    | is_false : ¬p → decidable
    | is_true  :  p → decidable
    -- END
    end hidden

Logically speaking, having an element ``t : decidable p`` is stronger than having an element ``t : p ∨ ¬p``; it enables us to define values of an arbitrary type depending on the truth value of ``p``. For example, for the expression ``if p then a else b`` to make sense, we need to know that ``p`` is decidable. That expression is syntactic sugar for ``ite p a b``, where ``ite`` is defined as follows:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    def ite (c : Prop) [d : decidable c] {α : Type} 
      (t e : α) : α :=
    decidable.rec_on d (λ hnc, e) (λ hc, t)
    -- END
    end hidden

The standard library also contains a variant of ``ite`` called ``dite``, the dependent if-then-else expression. It is defined as follows:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    def dite (c : Prop) [d : decidable c] {α : Type} 
      (t : c → α) (e : ¬ c → α) : α :=
    decidable.rec_on d (λ hnc : ¬ c, e hnc) (λ hc : c, t hc)
    -- END
    end hidden

That is, in ``dite c t e``, we can assume ``hc : c`` in the "then" branch, and ``hnc : ¬ c`` in the "else" branch. To make ``dite`` more convenient to use, Lean allows us to write ``if h : c then t else e`` instead of ``dite c (λ h : c, t) (λ h : ¬ c, e)``.

Without classical logic, we cannot prove that every proposition is decidable. But we can prove that *certain* propositions are decidable. For example, we can prove the decidability of basic operations like equality and comparisons on the natural numbers and the integers. Moreover, decidability is preserved under propositional connectives:

.. code-block:: lean

    #check @and.decidable
    -- Π {p q : Prop} [hp : decidable p] [hq : decidable q], 
    --   decidable (p ∧ q)

    #check @or.decidable
    #check @not.decidable
    #check @implies.decidable

Thus we can carry out definitions by cases on decidable predicates on the natural numbers:

.. code-block:: lean

    open nat

    def step (a b x : ℕ) : ℕ :=
    if x < a ∨ x > b then 0 else 1

    set_option pp.implicit true
    #print definition step

Turning on implicit arguments shows that the elaborator has inferred the decidability of the proposition ``x < a ∨ x > b``, simply by applying appropriate instances.

With the classical axioms, we can prove that every proposition is decidable. You can import the classical axioms and make the generic instance of decidability available by including this at the type of your file:

.. code-block:: lean

    open classical
    local attribute [instance] prop_decidable

Thereafter ``decidable p`` has an instance for every ``p``, and the elaborator infers that value quickly. Thus all theorems in the library that rely on decidability assumptions are freely available when you want to reason classically.

The ``decidable`` type class also provides a bit of small-scale automation for proving theorems. The standard library introduces the following definitions and notation:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    def as_true (c : Prop) [decidable c] : Prop :=
    if c then true else false

    def of_as_true {c : Prop} [h₁ : decidable c] (h₂ : as_true c) : 
      c :=
    match h₁, h₂ with
    | (is_true h_c),  h₂ := h_c
    | (is_false h_c), h₂ := false.elim h₂
    end

    notation `dec_trivial` := of_as_true (by tactic.triv)
    -- END

    end hidden

They work as follows. The expression ``as_true c`` tries to infer a decision procedure for ``c``, and, if it is successful, evaluates to either ``true`` or ``false``. In particular, if ``c`` is a true closed expression, ``as_true c`` will reduce definitionally to ``true``. On the assumption that ``as_true c`` holds, ``of_as_true`` produces a proof of ``c``. The notation ``dec_trivial`` puts it all together: to prove a target ``c``, it applies ``of_as_true`` and then using the ``triv`` tactic to prove ``as_true c``. By the previous observations, it will succeed any time the inferred decision procedure for ``c`` has enough information to evaluate, definitionally, to the ``is_true`` case. Here is an example of how ``dec_trivial`` can be used:

.. code-block:: lean

    example : 1 ≠ 0 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial

Try changing the ``3`` to ``10``, thereby rendering the expression false. The resulting error message complains that ``of_as_true (1 ≠ 0 ∧ (5 < 2 ∨ 10 < 7))`` is not definitionally equal to ``true``.


Managing Type Class Inference
-----------------------------

You can ask Lean for information about the classes and instances that are currently in scope:

.. code-block:: lean

    #print classes
    #print instances inhabited

At times, you may find that the type class inference fails to find an expected instance, or, worse, falls into an infinite loop and times out. To help debug in these situations, Lean enables you to request a trace of the search:

.. code-block:: lean

    set_option trace.class_instances true

If you add this to your file in Emacs mode and use ``C-c C-x`` to run an independent Lean process on your file, the output buffer will show a trace every time the type class resolution procedure is subsequently triggered.

You can also limit the search depth (the default is 32):

.. code-block:: lean

    set_option class.instance_max_depth 5

Remember also that in the Emacs Lean mode, tab completion works in ``set_option``, to help you find suitable options.

As noted above, the type class instances in a given context represent a Prolog-like program, which gives rise to a backtracking search. Both the efficiency of the program and the solutions that are found can depend on the order in which the system tries the instance. Instances which are declared last are tried first. Moreover, if instances are declared in other modules, the order in which they are tried depends on the order in which namespaces are opened. Instances declared in namespaces which are opened later are tried earlier.

You can change the order that type classes instances are tried by assigning them a *priority*. When an instance is declared, it is assigned a priority value ``std.priority.default``, defined to be 1000 in module ``init.core`` in the standard library. You can assign other priorities when defining an instance, and you can later change the priority with the ``attribute`` command. The following example illustrates how this is done:

.. code-block:: lean

    class foo :=
    (a : nat) (b : nat)

    @[priority std.priority.default+1]
    instance i1 : foo :=
    ⟨1, 1⟩

    instance i2 : foo :=
    ⟨2, 2⟩

    example : foo.a = 1 := rfl

    @[priority std.priority.default+20]
    instance i3 : foo :=
    ⟨3, 3⟩

    example : foo.a = 3 := rfl

    attribute [instance, priority 10] i3

    example : foo.a = 1 := rfl

    attribute [instance, priority std.priority.default-10] i1

    example : foo.a = 2 := rfl

.. _coercions_using_type_classes:

Coercions using Type Classes
----------------------------

The most basic type of coercion maps elements of one type to another. For example, a coercion from ``nat`` to ``int`` allows us to view any element ``n : nat`` as an element of ``int``. But some coercions depend on parameters; for example, for any type ``α``, we can view any element ``l : list α`` as an element of ``set α``, namely, the set of elements occurring in the list. The corresponding coercion is defined on the "family" of types ``list α``, parameterized by ``α``.

Lean allows us to declare three kinds of coercions:

-  from a family of types to another family of types
-  from a family of types to the class of sorts
-  from a family of types to the class of function types

The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family. The second kind of coercion allows us to view any element of a member of the source family as a type. The third kind of coercion allows us to view any element of the source family as a function. Let us consider each of these in turn.

In Lean, coercions are implemented on top of the type class resolution framework. We define a coercion from ``α`` to ``β`` by declaring an instance of ``has_coe α β``. For example, we can define a coercion from ``bool`` to ``Prop`` as follows:

.. code-block:: lean

    instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩

This enables us to use boolean terms in if-then-else expressions:

.. code-block:: lean

    instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩
    -- BEGIN
    #reduce if tt then 3 else 5
    #reduce if ff then 3 else 5
    -- END

We can define a coercion from ``list α`` to ``set α`` as follows:

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}
    def l : list nat := [3, 4]

    #check s ∪ l -- set nat

Coercions are only considered if the given and expected types do not contain metavariables at elaboration time. In the following example, when we elaborate the union operator, the type of ``[3, 2]`` is ``list ?m``, and a coercion will not be considered since it contains metavariables.

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    /- The following #check command produces an error. -/
    -- #check s ∪ [3, 2]
    -- END

We can work around this issue by using a type ascription.

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    #check s ∪ [(3:nat), 2]
    -- or
    #check s ∪ ([3, 2] : list nat)
    -- END

In the examples above, you may have noticed the symbol ``↑`` produced by the ``#check`` commands. It is the lift operator, ``↑t`` is notation for ``coe t``. We can use this operator to force a coercion to be introduced in a particular place. It is also helpful to make our intent clear, and work around limitations of the coercion resolution system.

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    #check s ∪ ↑[3, 2]

    variables n m : nat
    variable i : int
    #check i + ↑n + ↑m
    #check i + ↑(n + m)
    #check ↑n + i
    -- END

In the first two examples, the coercions are not strictly necessary since Lean will insert implicit nat → int coercions. However, ``#check n + i`` would raise an error, because the expected type of ``i`` is nat in order to match the type of n, and no int → nat coercion exists). In the third example, we therefore insert an explicit ``↑`` to coerce ``n`` to ``int``. 

The standard library defines a coercion from subtype ``{x : α // p x}`` to ``α`` as follows:

.. code-block:: lean

    namespace hidden
    universe u
    -- BEGIN
    instance coe_subtype {α : Type u} {p : α → Prop} : 
      has_coe {x // p x} α :=
    ⟨λ s, subtype.val s⟩
    -- END
    end hidden

Lean will also chain coercions as necessary. Actually, the type class ``has_coe_t`` is the transitive closure of ``has_coe``. You may have noticed that the type of ``coe`` depends on ``has_lift_t``, the transitive closure of the type class ``has_lift``, instead of ``has_coe_t``. Every instance of ``has_coe_t`` is also an instance of ``has_lift_t``, but the elaborator only introduces automatically instances of ``has_coe_t``. That is, to be able to coerce using an instance of ``has_lift_t``, we must use the operator ``↑``. In the standard library, we have the following instance:

.. code-block:: lean

    namespace hidden
    universes u v

    instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] : 
      has_lift (list a) (list b) :=
    ⟨λ l, list.map (@coe a b _) l⟩

    variables s : list nat
    variables r : list int
    #check ↑s ++ r

    end hidden

It is not an instance of ``has_coe`` because lists are frequently used for writing programs, and we do not want a linear-time operation to be silently introduced by Lean, and potentially mask mistakes performed by the user. By forcing the user to write ``↑``, she is making her intent clear to Lean.

Let us now consider the second kind of coercion. By the *class of sorts*, we mean the collection of universes ``Type u``. A coercion of the second kind is of the form

.. code-block:: text

    c : Π x1 : A1, ..., xn : An, F x1 ... xn → Type u

where ``F`` is a family of types as above. This allows us to write ``s : t`` whenever ``t`` is of type ``F a1 ... an``. In other words, the coercion allows us to view the elements of ``F a1 ... an`` as types. This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a ``Type``. For example, we can define a semigroup as follows:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, 
                   mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : 
      has_mul (S.carrier) :=
    ⟨S.mul⟩

In other words, a semigroup consists of a type, ``carrier``, and a multiplication, ``mul``, with the property that the multiplication is associative. The ``instance`` command allows us to write ``a * b`` instead of ``Semigroup.mul S a b`` whenever we have ``a b : S.carrier``; notice that Lean can infer the argument ``S`` from the types of ``a`` and ``b``. The function ``Semigroup.carrier`` maps the class ``Semigroup`` to the sort ``Type u``:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, 
                   mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩
    -- BEGIN
    #check Semigroup.carrier
    -- END

If we declare this function to be a coercion, then whenever we have a semigroup ``S : Semigroup``, we can write ``a : S`` instead of ``a : S.carrier``:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    -- BEGIN
    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := Type u, coe := λ S, S.carrier}

    example (S : Semigroup) (a b c : S) : 
      (a * b) * c = a * (b * c) :=
    Semigroup.mul_assoc _ a b c
    -- END

It is the coercion that makes it possible to write ``(a b c : S)``. Note that, we define an instance of ``has_coe_to_sort Semigroup`` instead of ``has_coe Semigroup Type``. The reason is that when Lean needs a coercion to sort, it only knows it needs a type, but, in general, the universe is not known. The field ``S`` in the class ``has_coe_to_sort`` is used to specify the universe we are coercing too.

By the *class of function types*, we mean the collection of Pi types ``Π z : B, C``. The third kind of coercion has the form

.. code-block:: text

    c : Π x1 : A1, ..., xn : An, y : F x1 ... xn, Π z : B, C

where ``F`` is again a family of types and ``B`` and ``C`` can depend on ``x1, ..., xn, y``. This makes it possible to write ``t s`` whenever ``t`` is an element of ``F a1 ... an``. In other words, the coercion enables us to view elements of ``F a1 ... an`` as functions. Continuing the example above, we can define the notion of a morphism between semigroups ``S1`` and ``S2``. That is, a function from the carrier of ``S1`` to the carrier of ``S2`` (note the implicit coercion) that respects the multiplication. The projection ``morphism.mor`` takes a morphism to the underlying function:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    -- BEGIN
    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    #check @morphism.mor
    -- END

As a result, it is a prime candidate for the third type of coercion.

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩


    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    -- BEGIN
    instance morphism_to_fun (S1 S2 : Semigroup) : 
      has_coe_to_fun (morphism S1 S2) :=
    { F   := λ _, S1 → S2,
      coe := λ m, m.mor }

    lemma resp_mul {S1 S2 : Semigroup} 
        (f : morphism S1 S2) (a b : S1) : 
      f (a * b) = f a * f b :=
    f.resp_mul a b

    example (S1 S2 : Semigroup) (f : morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
    calc
      f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
                ... = f a * f a * f a : by rw [resp_mul f]
    -- END

With the coercion in place, we can write ``f (a * a * a)`` instead of ``morphism.mor f (a * a * a)``. When the ``morphism``, ``f``, is used where a function is expected, Lean inserts the coercion. Similar to ``has_coe_to_sort``, we have yet another class ``has_coe_to_fun`` for the this class of coercions. The field ``F`` is used to specify function type we are coercing too. This type may depend on the type we are coercing from.

Finally, ``⇑f`` and ``↥S`` are notations for ``coe_fn f`` and ``coe_sort S``. They are the coercion operators for the function and sort classes.

We can instruct Lean's pretty-printer to hide the operators ``↑`` and ``⇑`` with ``set_option``.

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    instance morphism_to_fun (S1 S2 : Semigroup) : has_coe_to_fun (morphism S1 S2) :=
    { F   := λ _, S1 → S2,
      coe := λ m, m.mor }

    lemma resp_mul {S1 S2 : Semigroup} (f : morphism S1 S2) (a b : S1) : f (a * b) = f a * f b :=
    f.resp_mul a b

    -- BEGIN
    theorem test (S1 S2 : Semigroup) 
        (f : morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
    calc
      f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
                ... = f a * f a * f a : by rw [resp_mul f]

    #check @test
    set_option pp.coercions false
    #check @test
    -- END
