Require Import Coq.Reals.Reals.
Require Import ExtLib.Structures.Applicative.
Require Import Control.Barrier.

(** Notation for applicative functors *)
Notation "x <$> y" := (ap x y) (at level 30).

Definition liftA1 {T U : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U) (x : F T) : F U := (pure f) <$> x.

Definition liftA2 (T: Type -> Type) {app: Applicative T} (A B C: Type)
  (f: A -> B -> C) (a: T A) (b: T B): T C :=
  pure f <$> a <$> b.
Arguments liftA2 [_ _ _ _ _] _ _ _.

(** First, we define some notation to lift standard operators into
 ** the various logics. These define some operators for building
 ** terms in dL, but anything of type [StateVal T] is a term of
 ** type T.
 **)
Notation "a [+] b" := (liftA2 Rplus a b) (at level 50, left associativity).
Notation "a [-] b" := (liftA2 Rminus a b) (at level 50, left associativity).
Notation "a [*] b" := (liftA2 Rmult a b) (at level 40, left associativity).
Notation "a [^] n" := (liftA2 pow a n) (at level 40, left associativity).
Notation "a [/] b" := (liftA2 Rdiv a b) (at level 40, left associativity).
Notation "a [>=] b" := (liftA2 Rge a b) (at level 70, right associativity).
Notation "a [<=] b" := (liftA2 Rle a b) (at level 70, right associativity).
Notation "a [>] b" := (liftA2 Rgt a b) (at level 70, right associativity).
Notation "a [<] b" := (liftA2 Rlt a b) (at level 70, right associativity).
Notation "a [=] b" := (liftA2 (@eq R) a b) (at level 70, right associativity).
Notation "a [<>] b" := (liftA1 not (liftA2 (@eq R) a b)) (at level 70, right associativity).
Notation "[sqrt] e" := (liftA1 sqrt e) (at level 30, right associativity).
Notation "# x" := (pure x) (at level 20, right associativity).
Notation "c ?<= x [?] e1 [:] e2" :=
  (fun st => if Rle_dec (c st) x then e1 st else e2 st) (at level 80).

Notation "a [[+]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rplus a b) (at level 50, left associativity).
Notation "a [[-]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rminus a b) (at level 50, left associativity).
Notation "a [[*]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rmult a b) (at level 40, left associativity).
Notation "a [[^]] n" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ pow a n) (at level 40, left associativity).
Notation "a [[/]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rdiv a b) (at level 40, left associativity).
Notation "a [[>=]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rge a b) (at level 70, right associativity).
Notation "a [[<=]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rle a b) (at level 70, right associativity).
Notation "a [[>]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rgt a b) (at level 70, right associativity).
Notation "a [[<]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rlt a b) (at level 70, right associativity).
Notation "a [[=]] b" :=
  (@liftA2 _ (Applicative_FlowVal _) _ _ _ (@eq R) a b) (at level 70, right associativity).
Notation "a [[<>]] b" :=
  (@liftA1 _ _ _ (Applicative_FlowVal _) not (@liftA2 _ (Applicative_FlowVal _) _ _ _ (@eq R) a b))
    (at level 70, right associativity).
Notation "[[sqrt]] e" :=
  (@liftA1 _ _ _ (Applicative_FlowVal _) sqrt e) (at level 30, right associativity).
Notation "## x" := (@pure _ (Applicative_FlowVal _) _ x) (at level 20, right associativity).
Notation "c ??<= x [?] e1 [:] e2" :=
  (fun st' st => if Rle_dec (c st' st) x then e1 st' st else e2 st' st) (at level 80).
Notation "'d[' x ']'" := (fun st' st => x st') (at level 20).
Notation "'$[' e ']'" := (fun _ st => e st) (at level 20).

Notation "[] P" := (always P) (at level 70).
Notation "! P" := (start P) (at level 70).

Export ExtLib.Structures.Applicative.
