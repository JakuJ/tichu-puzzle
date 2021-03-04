Require Import Coq.Arith.PeanoNat.

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
  | Dragon
  | None.

Inductive Color : Type :=
  | Blue
  | Red
  | Green
  | Black
  | Unknown.

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
  | (Adam, Cezary) => True
  | (Hubert, Eliza) => True
  | (Urszula, Sonia) => True
  | (Tadeusz, Natalia) => True
  | (Mateusz, Irena) => True
  | _ => False
  end.

Definition place (a: Player): nat :=
  match a with
  | Adam | Cezary => 5
  | Hubert | Eliza  => 1
  | Urszula | Sonia => 2
  | Natalia | Tadeusz => 3
  | Irena | Mateusz => 4
  end.

Definition straight (a: Player): nat :=
  match a with
  | Sonia => 2
  | Hubert => 3
  | Urszula => 4
  | Eliza => 5
  | _ => 0 (* TODO: Refactor *)
  end.

Definition special (a: Player): Card :=
  match a with
  | Sonia => Phoenix
  | Hubert => Dog
  | Urszula => Dragon
  | Eliza => MahJong
  | _ => None (* TODO: Refactor *)
  end.

Definition color (a: Player): Color :=
  match a with
  | Sonia => Blue
  | Hubert => Red
  | Urszula => Green
  | Eliza => Black
  | _ => Unknown (* TODO: Refactor *)
  end.

(* We define a symmetric predicate for pairs. *)
Definition pair (a b: Player) := known_pair a b \/ known_pair b a.

(* By definition, a finalist is someone who took either the first or the second place. *)
Definition finalist (a:Player) := place a <= 2.

(*** SANITY CHECKS ***)

Lemma cannot_be_paired_with_self: forall a: Player, ~ pair a a.
Proof.
  intros.
  destruct a; unfold pair; unfold known_pair; intuition; auto.
Qed.

(* Prove that both players in a pair have the same place. *)
Lemma places_valid: forall p q : Player, pair p q -> place p = place q.
Proof.
  intros.
  unfold place.
  destruct p; destruct q; auto; unfold pair in H; unfold known_pair in H; destruct H; contradiction.
Qed.

(*** PROOFS FOR THE PUZZLE RULES ***)

(* Rule 1: Mateusz and Irena are paired, and they are neither 3rd nor 5th. *)
Lemma rule1: pair Mateusz Irena /\ place Mateusz <> 3 /\ place Irena <> 5.
Proof.
  split.
  - unfold pair.
    left.
    unfold known_pair.
    trivial.
  - split; unfold place; auto.
Qed.

(* Rule 2.1: The straight of the only man in the final didn't start with 4. *)
Lemma rule21: exists! p: Player, finalist p /\ man p /\ straight p <> 4.
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
          auto.
    - intros x H.
      destruct H.
      destruct H0.
      destruct x; unfold finalist in H; unfold place in H; apply Nat.leb_le in H; simpl in H; try discriminate; try unfold man in H0; intuition; discriminate.
Qed.

(* Rule 2.2: The straight of the owner of the Phoenix card didn't start with 4. *)
Lemma rule22: forall p: Player, special p = Phoenix -> straight p <> 4.
Proof.
  intros.
  replace p with Sonia.
  - unfold straight.
    auto.
  - destruct p; unfold special in H; try discriminate.
    tauto.
Qed.


(* Rule 3: Natalia finished higher than Cezary and Sonia \u2013 higher than Tadeusz. *)
Lemma rule3: place Natalia < place Cezary /\ place Sonia < place Tadeusz.
Proof.
  split; unfold place; auto.
Qed.

(* Rule 4: In the winning mixed pair it was Eliza who had the Mah Jong, and their straights were blue. *)
Lemma rule4: forall a: Player, pair a Eliza -> place a = 1 /\ man a /\ special Eliza = MahJong /\ color Eliza <> Blue /\ color a <> Blue.
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
Lemma rule5: forall p: Player, straight p = 2 -> color p <> Green /\ color p <> Red.
Proof.
  intros.
  destruct p; unfold straight in H; try discriminate.
  split; intuition; unfold color in H; discriminate.
Qed.

(* Rule 6: Tadeusz was paired with a woman. Adam was paired with a man. *)
Lemma rule6: forall p: Player, (pair Tadeusz p -> woman p) /\ (pair Adam p -> man p).
Proof.
  intros.
  split; intro; destruct p; unfold pair in H; unfold known_pair in H; intuition.
  unfold woman.
  all: unfold man; intuition; discriminate.
Qed.

(* Rule 7.1: The highest straight was black. *)
Lemma rule71: forall p: Player, straight p = 5 -> color p = Black.
Proof.
  intros.
  destruct p; unfold straight in H; try discriminate.
  auto.
Qed.

(* Rule 7.2: The person with the red straight had the Dog card. *)
Lemma rule72: forall p: Player, color p = Red -> special p = Dog.
Proof.
  intros.
  destruct p; unfold color in H; try discriminate.
  auto.
Qed.

(* Rule 7.3: Urszula was a runner-up and her straight was green. *)
Lemma rule73: place Urszula = 2 /\ color Urszula = Green.
Proof.
  auto.
Qed.

(* Our solution is correct as all rules have been proven to hold *)

End Tichu.
