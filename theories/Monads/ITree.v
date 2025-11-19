(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Section Defn.

  Context {E : Type -> Type} {R : Type}.

  Variant itreeF (itree : Type) :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : Type} (e : E X) (k : X -> itree)
  .

  CoInductive itree : Type := go
  { _observe : itreeF itree }.

End Defn.

Declare Scope itree_scope.
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree _ _ : clear implicits.
Arguments itreeF _ _ : clear implicits.

Create HintDb itree.
Notation itree' E R := (itreeF E R (itree E R)).
Definition observe {E R} (t : itree E R) : itree' E R := @_observe E R t.


Definition Ret {E} {R} (x : R) : itree E R :=
  go (@RetF E R (itree E R) x).
Definition Tau {E} {R} (t : itree E R) : itree E R :=
  go (@TauF E R (itree E R) t).
Definition Vis {E} {R} {X} (e : E X) (k : X -> itree E R) : itree E R :=
  go (@VisF E R (itree E R) X e k).

(* Definition subst {E : Type -> Type} {T U : Type} (k : T -> itree E U)
  : itree E T -> itree E U :=
  cofix _subst (u : itree E T) : itree E U :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_subst t)
    | VisF e h => Vis e (fun x => _subst (h x))
    end.

Definition bind {E : Type -> Type} {T U : Type} (u : itree E T) (k : T -> itree E U)
  : itree E U := subst u k.
    *)

Definition bind {E : Type -> Type} {T U : Type} (u : itree E T) (k : T -> itree E U)
  : itree E U :=
  let cofix _subst (u : itree E T) : itree E U :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_subst t)
    | VisF e h => Vis e (fun x => _subst (h x))
    end in _subst u.

Definition trigger {E : Type -> Type} {T : Type} (e : E T) : itree E T := Vis e Ret.

CoFixpoint hoist {E1 E2 R}
  (t : forall X, E1 X -> E2 X)
  (tr : itree E1 R) : itree E2 R :=
  match observe tr with
  | RetF r      => Ret r
  | TauF tr'    => Tau (hoist t tr')
  | VisF e k    => Vis (t _ e) (fun x => hoist t (k x))
  end.

Module MonadNotations.

  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.
  Open Scope monad.

  (* Notation "e1 ;; e2" := (@Vis _ _ _ e1%monad (fun _ => e2%monad))
    (at level 61, right associativity) : monad_scope.
  Notation "x <- c1 ;; c2" := (@Vis _ _ _ c1%monad (fun x => c2%monad))
    (at level 61, c1 at next level, right associativity) : monad_scope. *)

  Notation "e1 ;; e2" := (@bind _ _ _ e1%monad (fun _ => e2%monad))
    (at level 61, right associativity) : monad_scope.
  Notation "x <- c1 ;; c2" := (@bind _ _ _ c1%monad (fun x => c2%monad))
    (at level 61, c1 at next level, right associativity) : monad_scope.

End MonadNotations.
Import MonadNotations.

Crane Extract Skip itreeF.
Crane Extract Skip Tau.
Crane Extract Skip Ret.
Crane Extract Skip Vis.
Crane Extract Skip bind.
Crane Extract Skip trigger.
(* Crane Extract Monad itree [ bind := Vis , ret := Ret , hoist := hoist ] => "%t1". *)

(* TODO: Need a better solution to this. Both aesthetically
   and one that is more robust. *)
Crane Extract Monad itree [ bind := bind , ret := Ret ] => "%t1".
Crane Extract Inlined Constant observe => "".
(* Crane Extract Inlined Constant subst => "". *)

(* TODO: figure out how to get hoist working *)
(* Crane Extract Inlined Constant hoist => "%a0(%a1)". *)