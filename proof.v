Require Import Coq.Arith.PeanoNat.

Section Puzzle.

(*** INTRODUCTION ***)

(* We obtained a potential answer to the puzzle using Prolog.
   In this section, we will prove that if all rules hold for this
   result, then it must be the correct solution, as we assume
   the puzzle only has one. *)

(* S is a type of possible answers to the puzzle. *)
Variable S: Type.

(* A rule is a predicate on S. It is true if S satisfies the rule. *)
Definition Rule := S -> Prop.

(* 's' is a solution iff it satisfies all rules. *)
Definition solution (s: S) := forall r: Rule, r s.

(* We assume that there exists only one solution to the puzzle. *)
Axiom only_one_solution: exists! s: S, solution s.

(* If we find any solution, then it's the only one. *)
Lemma rules_sufficient: forall s: S, solution s -> ~ exists s2: S, solution s2 /\ s <> s2.
Proof.
  intros.
  unfold not at 1.
  intro C.
  inversion C as [x P].
  destruct P as [H1 N].
  pose proof only_one_solution as O.
  destruct O as [u U].
  unfold unique in U.
  destruct U as [SU EU].
  cut (u = s /\ u = x).
  + intros.
    destruct H0 as [US UX].
    rewrite -> US in UX.
    contradiction.
  + split; apply EU; assumption.
Qed.

End Puzzle.

(* We can now attempt to prove that our solution is in fact correct. *)

Section Tichu.

(*** DATA TYPES ***)

Inductive Player : Type :=
  | Adam
  | Cezary
  | Eliza
  | Hubert
  | Irena
  | Mateusz
  | Natalia
  | Sonia
  | Tadeusz
  | Urszula.

Inductive Card : Type :=
  | Phoenix
  | Dog
  | MahJong
  | Dragon.

Inductive Color : Type :=
  | Blue
  | Red
  | Green
  | Black.

(*** DEFINITIONS ***)

(* By definition, a man is either Adam, Cezary, Huber, Mateusz or Tadeusz. *)
Definition man (A: Player): Prop := A = Adam \/ A = Cezary \/ A = Hubert \/ A = Mateusz \/ A = Tadeusz.

(* By definition, a woman is a player who is not a man. *)
Definition woman (A: Player) : Prop := ~ man A.

(*** In this section we define a series of predicates
     that describe the mappings we assume to be correct
     and will thereby attempt to prove. ***)
Definition known_pair (a: Player) (b: Player): Prop :=
  match (a, b) with
  | (Adam, Cezary)      => True
  | (Hubert, Eliza)     => True
  | (Urszula, Sonia)    => True
  | (Tadeusz, Natalia)  => True
  | (Mateusz, Irena)    => True
  | _ => False
  end.

Definition place (a: Player): nat :=
  match a with
  | Hubert  | Eliza   => 1
  | Urszula | Sonia   => 2
  | Natalia | Tadeusz => 3
  | Irena   | Mateusz => 4
  | Adam    | Cezary  => 5
  end.

(* We define straights, special cards and colors in the option monad.
   This way we avoid partial functions. *)
Definition straight (a: Player): option nat :=
  match a with
  | Sonia   => Some 2
  | Hubert  => Some 3
  | Urszula => Some 4
  | Eliza   => Some 5
  | _       => None
  end.

Definition special (a: Player): option Card :=
  match a with
  | Sonia   => Some Phoenix
  | Hubert  => Some Dog
  | Urszula => Some Dragon
  | Eliza   => Some MahJong
  | _       => None
  end.

Definition color (a: Player): option Color :=
  match a with
  | Sonia   => Some Blue
  | Hubert  => Some Red
  | Urszula => Some Green
  | Eliza   => Some Black
  | _       => None
  end.

(* We define a symmetric predicate for pairs. *)
Definition pair (a b: Player) := known_pair a b \/ known_pair b a.

(* By definition, a finalist is someone who took either the first or the second place. *)
Definition finalist (a:Player) := place a <= 2.

(*** SANITY CHECKS ***)

Fact cannot_be_paired_with_self: forall a: Player, ~ pair a a.
Proof.
  intros.
  destruct a; unfold pair; unfold known_pair; intuition; auto.
Qed.

(* Prove that both players in a pair have the same place. *)
Fact places_valid: forall p q : Player, pair p q -> place p = place q.
Proof.
  intros.
  unfold place.
  destruct p; destruct q; auto; unfold pair in H; unfold known_pair in H; destruct H; contradiction.
Qed.

(*** PROOFS FOR THE PUZZLE RULES ***)

(* Let's introduce some notation for comparing values in the option monad. *)
Notation "A '=S=' S" := (A = Some S)
(at level 70, no associativity).

(* When we say that someone's special card is not a Dragon, 
   we also assume that they do have some other special card. *)
Notation "A '<S>' S" := (A <> Some S /\ A <> None)
(at level 70, no associativity).

(* Rule 1: Mateusz and Irena are paired, and they are neither 3rd nor 5th. *)
Fact rule1: pair Mateusz Irena /\ place Mateusz <> 3 /\ place Irena <> 5.
Proof.
  split.
  - unfold pair.
    left.
    unfold known_pair.
    trivial.
  - split; unfold place; auto.
Qed.

(* Rule 2.1: The straight of the only man in the final didn't start with 4. *)
Fact rule21: exists! p: Player, finalist p /\ man p /\ straight p <S> 4.
Proof.
  exists Hubert.
  unfold unique.
  split.
    - split.
      + unfold finalist.
        unfold place.
        auto.
      + split.
        * unfold man.
          tauto.
        * unfold straight.
          split; intro C; inversion C.
    - intros x H.
      destruct H.
      destruct H0.
      destruct x; unfold finalist in H; unfold place in H; apply Nat.leb_le in H; simpl in H; try discriminate; try unfold man in H0; intuition; discriminate.
Qed.

(* Rule 2.2: The straight of the owner of the Phoenix card didn't start with 4. *)
Fact rule22: forall p: Player, special p =S= Phoenix -> straight p <S> 4.
Proof.
  intros.
  replace p with Sonia.
  - unfold straight.
    split; intros C; inversion C.
  - destruct p; unfold special in H; try discriminate.
    tauto.
Qed.

(* Rule 3: Natalia finished higher than Cezary and Sonia - higher than Tadeusz. *)
Fact rule3: place Natalia < place Cezary /\ place Sonia < place Tadeusz.
Proof.
  split; unfold place; auto.
Qed.

(* Rule 4: In the winning mixed pair it was Eliza who had the Mah Jong, and their straights were blue. *)
Fact rule4: forall a: Player, pair a Eliza -> place a = 1 /\ man a /\ special Eliza =S= MahJong /\ color Eliza <S> Blue /\ color a <S> Blue.
Proof.
  intros.
  replace a with Hubert.
  - split. unfold place. trivial.
    split. unfold man. auto.
    split. unfold special. trivial.
    split; unfold color; intuition; discriminate.
  - destruct a; unfold pair in H; destruct H; unfold known_pair in H; tauto.
Qed.

(* Rule 5: The lowest straight was neither green nor red. *)
Fact rule5: forall p: Player, straight p =S= 2 -> color p <S> Green /\ color p <S> Red.
Proof.
  intros.
  destruct p; unfold straight in H; try discriminate.
  split; intuition; unfold color in H; discriminate.
Qed.

(* Rule 6: Tadeusz was paired with a woman. Adam was paired with a man. *)
Fact rule6: forall p: Player, (pair Tadeusz p -> woman p) /\ (pair Adam p -> man p).
Proof.
  intros.
  split; intro; destruct p; unfold pair in H; unfold known_pair in H; intuition.
  unfold woman.
  all: unfold man; intuition; discriminate.
Qed.

(* Rule 7.1: The highest straight was black. *)
Fact rule71: forall p: Player, straight p =S= 5 -> color p =S= Black.
Proof.
  intros.
  destruct p; unfold straight in H; try discriminate.
  auto.
Qed.

(* Rule 7.2: The person with the red straight had the Dog card. *)
Fact rule72: forall p: Player, color p =S= Red -> special p =S= Dog.
Proof.
  intros.
  destruct p; unfold color in H; try discriminate.
  auto.
Qed.

(* Rule 7.3: Urszula was a runner-up and her straight was green. *)
Fact rule73: place Urszula = 2 /\ color Urszula =S= Green.
Proof.
  auto.
Qed.

(* Our solution is correct as all rules have been proven to hold *)

End Tichu.
