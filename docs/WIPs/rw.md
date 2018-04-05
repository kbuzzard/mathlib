# more on rw

The `rewrite` tactic is documented (here in the reference manual)[https://leanprover.github.io/reference/tactics.html#the-rewriter]. Here are a couple of things it doesn't say.

```lean
example (a b c d e : ℕ) (H : b = c) : b + a = b + a + a + c := begin
rw H, -- goal now ⊢ c + a = c + a + a + c
rw add_comm, -- goal now ⊢ a + c = a + c + a + c
admit,
end
```

We see from the first line that `rw` will rewrite all matches it finds.
`rw H` translates as "take every `b` and replace it with a `c`", as
can be seen from the goal after `rw H`.

However `rw add_comm` does not take every `+` in the goal and apply
`add_comm` to it. What is going on? Firstly note that `add_comm`
is actually `add_comm : ∀ (x y : ?M_1), x + y = y + x`, so Lean has
to decide how to actually apply this lemma by choosing what `x` and `y` are.
Next remember (or
type `set_option pp.notation false` and observe) that `c + a = c + a + a + c`
is really
`add c a = add (add (add c a) a) c)`.

What `rw add_comm` does (at least what I am assuming it does based on these
tests) is that it looks for an `add` in the goal, and when it runs into the
first one (namely `add c a`) it decides that this is the one it will rewrite.
It then decides that it's going to rewrite all `add c a`'s as `add a c`'s,
and then ignores all the other adds which don't match this pattern.

Note in particular that `rw add_comm` does not commute with `eq.symm`!