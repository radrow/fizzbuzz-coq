Definition FizzBuzzInteger := {n : N | n mod 5 <> 0 /\ n mod 3 <> 0}.


Inductive FizzBuzzEntry : Set :=
| Shadow : FizzBuzzShadow -> FizzBuzzEntry
| Num : FizzBuzzInteger -> FizzBuzzEntry
.


Inductive FizzBuzzShadow : Set :=
| Fizz : {n : N | n mod 3 = 0 /\ n mod 5 <> 0} -> FizzBuzzShadow
| Buzz : {n : N | n mod 3 <> 0 /\ n mod 5 = 0} -> FizzBuzzShadow
| FizzBuzz : {n : N | n mod 3 = 0 /\ n mod 5 = 0} -> FizzBuzzShadow
.


Definition initial : FizzBuzzEntry.
  refine (Num (exist _ 1 _)).
  split.
  * assert (1 mod 3 = 1).
    ** auto.
    ** rewrite H.
       zify. omega.
  *  assert (1 mod 5 = 1).
    ** auto.
    ** rewrite H.
       zify. omega.
Qed.


Definition toNat (previousEntry : FizzBuzzEntry): N :=
  match previousEntry with
  | Shadow (Fizz (exist _ shadowed _))     => shadowed
  | Shadow (Buzz (exist _ shadowed _))     => shadowed
  | Shadow (FizzBuzz (exist _ shadowed _)) => shadowed
  | Num (exist _ n _)                      => n
  end.


Definition next (previousEntry : FizzBuzzEntry): FizzBuzzEntry :=
  fromNat (toNat previousEntry + 1).


Definition fromNat (n : N): FizzBuzzEntry.
  refine (match (n mod 3 ?= 0, n mod 5 ?= 0)
                as cmp
                return (n mod 3 ?= 0, n mod 5 ?= 0) = cmp -> FizzBuzzEntry with
          | (Eq, Eq) => fun pf => _
          | (Eq, Gt) => fun pf => _
          | (Gt, Eq) => fun pf => _
          | (Gt, Gt) => fun pf => _
          | _ => _
          end eq_refl).
  * apply pair_equal_spec in pf.
    destruct pf.
    apply N.compare_eq_iff in H.
    apply N.compare_eq_iff in H0.
    assert (n mod 3 = 0 /\ n mod 5 = 0); auto.
    apply (Shadow (FizzBuzz (exist _ n H1))).
  * intros.
    apply pair_equal_spec in H.
    destruct H.
    destruct H.
    exfalso.
    apply N.compare_lt_iff in H0.
    assert (0 <= (n mod 5)).
    ** apply N.mod_bound_pos.
       *** destruct n.
           **** zify. omega.
           **** apply N.lt_succ_r. apply N.compare_gt_iff. auto.
       *** zify. omega.
    ** assert (n mod 5 < 0).
       *** auto.
       *** assert ((n mod 5 ?= 0) <> Lt).
           **** apply N.compare_0_r.
           **** contradiction.
  * apply pair_equal_spec in pf.
    destruct pf.
    apply N.compare_eq_iff in H.
    apply N.compare_gt_iff in H0.
    assert (n mod 3 = 0 /\ n mod 5 <> 0).
    ** intuition.
    ** apply (Shadow (Fizz (exist _ n H1))).
  * intros.
    apply pair_equal_spec in H.
    destruct H.
    exfalso.
    *** assert ((n mod 3 ?= 0) <> Lt).
        **** apply N.compare_0_r.
        **** contradiction.
  * apply pair_equal_spec in pf.
    destruct pf.
    apply N.compare_eq_iff in H0.
    apply N.compare_gt_iff in H.
    assert (n mod 3 <> 0 /\ n mod 5 = 0).
    ** intuition.
    ** apply (Shadow (Buzz (exist _ n H1))).
  * intros.
    apply pair_equal_spec in H.
    destruct H.
    exfalso.
    *** assert ((n mod 5 ?= 0) <> Lt).
        **** apply N.compare_0_r.
        **** contradiction.
  * apply pair_equal_spec in pf.
    destruct pf.
    apply N.compare_gt_iff in H0.
    apply N.compare_gt_iff in H.
    assert (n mod 3 <> 0 /\ n mod 5 <> 0).
    ** intuition.
    ** apply (Num (exist _ n H1)).
Defined.
