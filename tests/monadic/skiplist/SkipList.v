(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   STM-based Skip List implementation
   Ported from Haskell's tskiplist package:
   https://hackage.haskell.org/package/tskiplist-1.0.1/docs/Control-Concurrent-STM-TSkipList.html

   A skip list is a probabilistic data structure with dictionary operations.
   In contrast to a balanced tree, a skip list does not need any expensive
   rebalancing operation, making it suitable for concurrent programming.

   Reference: William Pugh. Skip Lists: A Probabilistic Alternative to Balanced Trees.

   Implementation note: Since Rocq's positivity checker doesn't allow recursive
   types through TVar, we use an axiomatized Node type that extracts to C++
   shared_ptr-based nodes.
*)

From Stdlib Require Import List Bool Arith.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.STM.
From Corelib Require Import PrimInt63.

Import ListNotations.
Import MonadNotations.
Set Implicit Arguments.

Module SkipList.

(* ========================================================================= *)
(*                              Configuration                                *)
(* ========================================================================= *)

(* Maximum number of levels - supports up to 2^16 elements efficiently *)
Definition maxLevels : nat := 16.

(* ========================================================================= *)
(*                         Random Level Generation                           *)
(* ========================================================================= *)

(* Axiom for random number generation *)
Module Random_axioms.
  Axiom irandomInt : int -> IO_axioms.iIO int.
End Random_axioms.

Crane Extract Skip Module Random_axioms.
Import Random_axioms.

Definition randomInt (bound : int) : IO int := trigger (irandomInt bound).

Crane Extract Inlined Constant randomInt =>
  "(std::rand() % %a0)" From "cstdlib".

(* Choose a random level for a new node *)
Fixpoint chooseLevel_aux (fuel : nat) (acc : nat) (maxLvl : nat) : IO nat :=
  match fuel with
  | O => Ret acc
  | S fuel' =>
      if Nat.leb maxLvl acc then Ret acc
      else
        r <- randomInt 100%int63 ;;
        if ltb r 50%int63 then
          chooseLevel_aux fuel' (S acc) maxLvl
        else
          Ret acc
  end.

Definition chooseLevel : IO nat := chooseLevel_aux maxLevels 0 maxLevels.

(* ========================================================================= *)
(*                     Axiomatized Node Type                                 *)
(* ========================================================================= *)

(* Since Rocq doesn't allow recursive types through TVar, we axiomatize
   the node structure and provide extraction rules to C++. *)

Module Node_axioms.
  (* NodeRef is a reference to a node - extracted to shared_ptr<Node<K,V>> *)
  Axiom NodeRef : Type -> Type -> Type.

  (* Node operations *)
  Axiom inewNode : forall {K V : Type}, K -> V -> nat -> STM_axioms.iSTM (NodeRef K V).
  Axiom igetKey : forall {K V : Type}, NodeRef K V -> K.
  Axiom ireadValue : forall {K V : Type}, NodeRef K V -> STM_axioms.iSTM V.
  Axiom iwriteValue : forall {K V : Type}, NodeRef K V -> V -> STM_axioms.iSTM void.
  Axiom igetLevel : forall {K V : Type}, NodeRef K V -> nat.
  Axiom ireadNext : forall {K V : Type}, NodeRef K V -> nat -> STM_axioms.iSTM (option (NodeRef K V)).
  Axiom iwriteNext : forall {K V : Type}, NodeRef K V -> nat -> option (NodeRef K V) -> STM_axioms.iSTM void.
End Node_axioms.

Crane Extract Skip Module Node_axioms.
Import Node_axioms.

(* Wrap axioms in STM monad *)
Definition newNode {K V : Type} (k : K) (v : V) (level : nat) : STM (NodeRef K V) :=
  trigger (inewNode k v level).

Definition getKey {K V : Type} (n : NodeRef K V) : K := igetKey n.

Definition readValue {K V : Type} (n : NodeRef K V) : STM V :=
  trigger (ireadValue n).

Definition writeValue {K V : Type} (n : NodeRef K V) (v : V) : STM void :=
  trigger (iwriteValue n v).

Definition getLevel {K V : Type} (n : NodeRef K V) : nat := igetLevel n.

Definition readNext {K V : Type} (n : NodeRef K V) (level : nat) : STM (option (NodeRef K V)) :=
  trigger (ireadNext n level).

Definition writeNext {K V : Type} (n : NodeRef K V) (level : nat) (next : option (NodeRef K V)) : STM void :=
  trigger (iwriteNext n level next).

(* Extraction rules for Node operations *)
Crane Extract Inlined Constant NodeRef => "std::shared_ptr<SkipNode<%t0, %t1>>" From "skipnode.h".
Crane Extract Inlined Constant newNode => "SkipNode<%t0, %t1>::create(%a0, %a1, %a2)".
Crane Extract Inlined Constant getKey => "%a0->key".
Crane Extract Inlined Constant readValue => "stm::readTVar<%t1>(%a0->value)".
Crane Extract Inlined Constant writeValue => "stm::writeTVar<%t1>(%a0->value, %a1)".
Crane Extract Inlined Constant getLevel => "%a0->level".
Crane Extract Inlined Constant readNext => "stm::readTVar<std::optional<std::shared_ptr<SkipNode<%t0, %t1>>>>(%a0->forward[%a1])".
Crane Extract Inlined Constant writeNext => "stm::writeTVar<std::optional<std::shared_ptr<SkipNode<%t0, %t1>>>>(%a0->forward[%a1], %a2)".

(* ========================================================================= *)
(*                            Skip List Structure                            *)
(* ========================================================================= *)

Record TSkipList (K V : Type) := mkTSkipList {
  slHead     : NodeRef K V;      (* Sentinel head node *)
  slMaxLevel : nat;              (* Maximum allowed levels *)
  slLevel    : TVar nat          (* Current highest level in use *)
}.

Arguments mkTSkipList {K V} _ _ _.
Arguments slHead {K V} _.
Arguments slMaxLevel {K V} _.
Arguments slLevel {K V} _.

(* ========================================================================= *)
(*                           Core Operations                                 *)
(* ========================================================================= *)

Section Operations.

Variable K V : Type.
Variable ltK : K -> K -> bool.   (* less-than comparison on keys *)
Variable eqK : K -> K -> bool.   (* equality on keys *)

(* Search fuel - prevents infinite loops *)
Definition searchFuel : nat := 1000.

(* Find predecessor at a given level *)
Fixpoint findPred_aux (fuel : nat) (curr : NodeRef K V) (target : K) (level : nat)
  : STM (NodeRef K V) :=
  match fuel with
  | O => Ret curr
  | S fuel' =>
      nextOpt <- readNext curr level ;;
      match nextOpt with
      | None => Ret curr
      | Some next =>
          if ltK (getKey next) target then
            findPred_aux fuel' next target level
          else
            Ret curr
      end
  end.

Definition findPred (curr : NodeRef K V) (target : K) (level : nat) : STM (NodeRef K V) :=
  findPred_aux searchFuel curr target level.

(* Collect update path from current level down to 0 *)
Fixpoint findPath_aux (fuel : nat) (curr : NodeRef K V) (target : K) (level : nat)
  (acc : list (NodeRef K V)) : STM (list (NodeRef K V)) :=
  match fuel with
  | O => Ret acc
  | S fuel' =>
      pred <- findPred curr target level ;;
      let acc' := pred :: acc in
      match level with
      | O => Ret acc'
      | S level' => findPath_aux fuel' pred target level' acc'
      end
  end.

Definition findPath (sl : TSkipList K V) (target : K) : STM (list (NodeRef K V)) :=
  lvl <- readTVar (slLevel sl) ;;
  findPath_aux searchFuel (slHead sl) target lvl [].

(* ------------------------------------------------------------------------ *)
(*                              lookup                                      *)
(* ------------------------------------------------------------------------ *)

Definition lookup (k : K) (sl : TSkipList K V) : STM (option V) :=
  path <- findPath sl k ;;
  match path with
  | [] => Ret None
  | pred0 :: _ =>
      nextOpt <- readNext pred0 0 ;;
      match nextOpt with
      | None => Ret None
      | Some node =>
          if eqK (getKey node) k then
            v <- readValue node ;;
            Ret (Some v)
          else
            Ret None
      end
  end.

(* ------------------------------------------------------------------------ *)
(*                              insert                                      *)
(* ------------------------------------------------------------------------ *)

(* Link new node at one level *)
Definition linkAtLevel (pred newNode : NodeRef K V) (level : nat) : STM void :=
  oldNext <- readNext pred level ;;
  writeNext pred level (Some newNode) ;;
  writeNext newNode level oldNext.

(* Link at all levels from 0 to nodeLevel *)
Fixpoint linkNode_aux (preds : list (NodeRef K V)) (newNode : NodeRef K V) (level : nat)
  : STM void :=
  match preds, level with
  | [], _ => Ret ghost
  | pred :: rest, O => linkAtLevel pred newNode 0
  | pred :: rest, S level' =>
      linkAtLevel pred newNode level ;;
      linkNode_aux rest newNode level'
  end.

(* Extend path with head node for levels above slLevel *)
(* path is [level0_pred, level1_pred, ..., levelN_pred] *)
(* We need to extend it to include head for higher levels *)
Definition extendPath (path : list (NodeRef K V)) (head : NodeRef K V) (needed : nat) : list (NodeRef K V) :=
  let have := length path in
  if Nat.leb needed have then path
  else path ++ repeat head (needed - have).

Definition linkNode (path : list (NodeRef K V)) (newNode : NodeRef K V) : STM void :=
  let lvl := getLevel newNode in
  let relevantPath := firstn (S lvl) path in
  linkNode_aux (rev relevantPath) newNode lvl.

Definition insert (k : K) (v : V) (sl : TSkipList K V) (newLevel : nat) : STM void :=
  path <- findPath sl k ;;
  (* Extend path with head for levels above current slLevel *)
  let fullPath := extendPath path (slHead sl) (S newLevel) in
  match fullPath with
  | [] => Ret ghost
  | pred0 :: _ =>
      nextOpt <- readNext pred0 0 ;;
      match nextOpt with
      | Some existing =>
          if eqK (getKey existing) k then
            writeValue existing v
          else
            newNode <- newNode k v newLevel ;;
            linkNode fullPath newNode ;;
            curLvl <- readTVar (slLevel sl) ;;
            if Nat.ltb curLvl newLevel then
              writeTVar (slLevel sl) newLevel
            else
              Ret ghost
      | None =>
          newNode <- newNode k v newLevel ;;
          linkNode fullPath newNode ;;
          curLvl <- readTVar (slLevel sl) ;;
          if Nat.ltb curLvl newLevel then
            writeTVar (slLevel sl) newLevel
          else
            Ret ghost
      end
  end.

(* ------------------------------------------------------------------------ *)
(*                              remove                                      *)
(* ------------------------------------------------------------------------ *)

Definition unlinkAtLevel (pred target : NodeRef K V) (level : nat) : STM void :=
  targetNext <- readNext target level ;;
  writeNext pred level targetNext.

Fixpoint unlinkNode_aux (preds : list (NodeRef K V)) (target : NodeRef K V) (level : nat)
  : STM void :=
  match preds, level with
  | [], _ => Ret ghost
  | pred :: rest, O => unlinkAtLevel pred target 0
  | pred :: rest, S level' =>
      unlinkAtLevel pred target level ;;
      unlinkNode_aux rest target level'
  end.

Definition unlinkNode (path : list (NodeRef K V)) (target : NodeRef K V) : STM void :=
  let lvl := getLevel target in
  let relevantPath := firstn (S lvl) path in
  unlinkNode_aux (rev relevantPath) target lvl.

Definition remove (k : K) (sl : TSkipList K V) : STM void :=
  path <- findPath sl k ;;
  match path with
  | [] => Ret ghost
  | pred0 :: _ =>
      nextOpt <- readNext pred0 0 ;;
      match nextOpt with
      | Some node =>
          if eqK (getKey node) k then
            (* Extend path for the target node's level *)
            let fullPath := extendPath path (slHead sl) (S (getLevel node)) in
            unlinkNode fullPath node
          else
            Ret ghost
      | None => Ret ghost
      end
  end.

(* ------------------------------------------------------------------------ *)
(*                              minimum                                     *)
(* ------------------------------------------------------------------------ *)

Definition minimum (sl : TSkipList K V) : STM (option (K * V)) :=
  firstOpt <- readNext (slHead sl) 0 ;;
  match firstOpt with
  | None => Ret None
  | Some node =>
      v <- readValue node ;;
      Ret (Some (getKey node, v))
  end.

(* ------------------------------------------------------------------------ *)
(*                              member                                      *)
(* ------------------------------------------------------------------------ *)

Definition member (k : K) (sl : TSkipList K V) : STM bool :=
  result <- lookup k sl ;;
  Ret (match result with Some _ => true | None => false end).

End Operations.

(* ========================================================================= *)
(*                            Construction                                   *)
(* ========================================================================= *)

Definition create {K V : Type} (dummyKey : K) (dummyVal : V) : STM (TSkipList K V) :=
  headNode <- newNode dummyKey dummyVal (maxLevels - 1) ;;
  lvlTV <- newTVar 0 ;;
  Ret (mkTSkipList headNode maxLevels lvlTV).

Definition createIO {K V : Type} (dummyKey : K) (dummyVal : V) : IO (TSkipList K V) :=
  atomically (create dummyKey dummyVal).

End SkipList.

(* ========================================================================= *)
(*                              Test Module                                  *)
(* ========================================================================= *)

Module skiplist_test.
Import SkipList.

Definition nat_lt (x y : nat) : bool := Nat.ltb x y.
Definition nat_eq (x y : nat) : bool := Nat.eqb x y.

(* STM test functions *)
Definition stm_test_insert_lookup (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  (* Use multiple levels to test skip list structure *)
  insert nat_lt nat_eq 5 50 sl 2 ;;
  insert nat_lt nat_eq 3 30 sl 1 ;;
  insert nat_lt nat_eq 7 70 sl 0 ;;
  insert nat_lt nat_eq 1 10 sl 1 ;;

  v5 <- lookup nat_lt nat_eq 5 sl ;;
  v3 <- lookup nat_lt nat_eq 3 sl ;;
  v7 <- lookup nat_lt nat_eq 7 sl ;;
  v1 <- lookup nat_lt nat_eq 1 sl ;;
  v9 <- lookup nat_lt nat_eq 9 sl ;;

  let c1 := match v5 with Some 50 => true | _ => false end in
  let c2 := match v3 with Some 30 => true | _ => false end in
  let c3 := match v7 with Some 70 => true | _ => false end in
  let c4 := match v1 with Some 10 => true | _ => false end in
  let c5 := match v9 with None => true | _ => false end in

  Ret (andb c1 (andb c2 (andb c3 (andb c4 c5)))).

Definition stm_test_delete (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  (* Use multiple levels for delete test too *)
  insert nat_lt nat_eq 5 50 sl 2 ;;
  insert nat_lt nat_eq 3 30 sl 1 ;;
  insert nat_lt nat_eq 7 70 sl 0 ;;

  (* Delete node at level 2 *)
  remove nat_lt nat_eq 5 sl ;;

  v5 <- lookup nat_lt nat_eq 5 sl ;;
  v3 <- lookup nat_lt nat_eq 3 sl ;;
  v7 <- lookup nat_lt nat_eq 7 sl ;;

  let c1 := match v5 with None => true | _ => false end in
  let c2 := match v3 with Some 30 => true | _ => false end in
  let c3 := match v7 with Some 70 => true | _ => false end in

  Ret (andb c1 (andb c2 c3)).

Definition stm_test_update (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq 5 50 sl 0 ;;
  insert nat_lt nat_eq 5 500 sl 0 ;;

  v <- lookup nat_lt nat_eq 5 sl ;;
  Ret (match v with Some 500 => true | _ => false end).

Definition stm_test_minimum (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq 5 50 sl 0 ;;
  insert nat_lt nat_eq 3 30 sl 0 ;;
  insert nat_lt nat_eq 7 70 sl 0 ;;

  minOpt <- minimum sl ;;
  Ret (match minOpt with
       | Some (3, 30) => true
       | _ => false
       end).

(* IO wrappers *)
Definition test_insert_lookup (_ : void) : IO bool :=
  atomically (stm_test_insert_lookup ghost).

Definition test_delete (_ : void) : IO bool :=
  atomically (stm_test_delete ghost).

Definition test_update (_ : void) : IO bool :=
  atomically (stm_test_update ghost).

Definition test_minimum (_ : void) : IO bool :=
  atomically (stm_test_minimum ghost).

Definition run_tests : IO nat :=
  r1 <- test_insert_lookup ghost ;;
  r2 <- test_delete ghost ;;
  r3 <- test_update ghost ;;
  r4 <- test_minimum ghost ;;
  let passed := (if r1 then 1 else 0) +
                (if r2 then 1 else 0) +
                (if r3 then 1 else 0) +
                (if r4 then 1 else 0) in
  Ret passed.

End skiplist_test.

Crane Extraction "skiplist" skiplist_test.
