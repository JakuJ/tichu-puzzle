Require Import Coq.Arith.PeanoNat.

Section Puzzle.

(*** INTRODUCTION ***)

(* We obtained a potential answer to the puzzle using Prolog.
   In this section, we will prove that if all rules hold for this
   result, then it must be the correct solution, as we assume
   the puzzle only has one. *)

(* S is a type of possible answers to the puzzle. *)
Variable S : Type.

(* A rule is a predicate on S. It is true if S satisfies the rule. *)
Definition Rule := S -> Prop.

(* 's' is a solution iff it satisfies all rules. *)
Definition solution (s: S) := forall r: Rule, r s.

(* We assume that there exists only one solution to the puzzle. *)
Conjecture only_one_solution: exists! s: S, solution s.

(* If we find any solution, then it's the only one. *)
Lemma rules_sufficient: forall s: S, solution s -> ~ exists s2: S, solution s2 /\ s <> s2.
Proof.
  (* Let's call our solution x *)
  intros x X C.
  (* Assume the other solution would be y *)
  inversion C as [y [Y N]].
  (* Use the assumption that there is only one solution, u. *)
  pose proof only_one_solution as [u U].
  unfold unique in U.
  destruct U as [U SU].
  (* u, as the only solution, must be equal to x and y *)
  apply SU in X, Y.
  (* this leads us to contradiction: u = x = y, but x <> y *)
  rewrite X in Y.
  contradiction.
Qed.

End Puzzle.

(* We can now attempt to prove that our solution is in fact correct. *)

Section Tichu.

(*** DATA TYPES ***)

Inductive Player :=
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

Inductive Color := Blue | Red | Green | Black.
Inductive Card := Phoenix | Dog | MahJong | Dragon.

(*** DEFINITIONS ***)

(* By definition, a man is either Adam, Cezary, Huber, Mateusz or Tadeusz. *)
Definition man (p : Player) : Prop :=
  match p with
  | Adam | Cezary | Hubert | Mateusz | Tadeusz => True
  | _ => False
  end.

(* By definition, a woman is a player who is not a man. *)
Definition woman (p: Player) := ~ man p.

(*** In this section we define a series of predicates
     that describe the mappings we assume to be correct
     and will thereby attempt to prove. ***)
Definition known_pair (p q: Player) : Prop :=
  match (p, q) with
  | (Adam, Cezary)      => True
  | (Hubert, Eliza)     => True
  | (Urszula, Sonia)    => True
  | (Tadeusz, Natalia)  => True
  | (Mateusz, Irena)    => True
  | _ => False
  end.

Definition place (p: Player) : nat :=
  match p with
  | Hubert  | Eliza   => 1
  | Urszula | Sonia   => 2
  | Natalia | Tadeusz => 3
  | Irena   | Mateusz => 4
  | Adam    | Cezary  => 5
  end.

(* We define straights, special cards and colors in the option monad.
   This way we avoid partial functions. *)
Definition straight (p: Player) : option nat :=
  match p with
  | Sonia   => Some 2
  | Hubert  => Some 3
  | Urszula => Some 4
  | Eliza   => Some 5
  | _       => None
  end.

Definition special (p: Player) : option Card :=
  match p with
  | Sonia   => Some Phoenix
  | Hubert  => Some Dog
  | Urszula => Some Dragon
  | Eliza   => Some MahJong
  | _       => None
  end.

Definition color (p: Player) : option Color :=
  match p with
  | Sonia   => Some Blue
  | Hubert  => Some Red
  | Urszula => Some Green
  | Eliza   => Some Black
  | _       => None
  end.

(* We define a symmetric predicate for pairs. *)
Definition pair (p q: Player) := known_pair p q \/ known_pair q p.

(* By definition, a finalist is someone who took either the first or the second place. *)
Definition finalist (p: Player) := place p <= 2.

(*** SANITY CHECKS ***)

(* Nobody can be paired with themselves. *)
Lemma cannot_be_paired_with_self: forall p: Player, ~ pair p p.
Proof.
  intro.
  (* check all players *)
  destruct p.
  (* evaluate pairs *)
  all: unfold pair, known_pair; tauto.
Qed.

(* Both players in a pair have the same place. *)
Lemma places_valid: forall p q : Player, pair p q -> place p = place q.
Proof.
  intros.
  (* brute-force all combinations *)
  destruct p, q.
  (* evaluate pairs *)
  all: unfold pair, known_pair in H; tauto.
Qed.

(*** NOTATION AND TACTICS ***)

(* A shorthand for equality with Some value. *)
Notation "A '=S=' B" := (A = Some B)
(at level 70, no associativity).

(* A shorthand for inequality of Some values.
   Useful, because whenever we say that someone's
   special card is not a Dragon, we also assume
   that they do have some other special card. *)
Notation "A '<S>' B" := (A <> Some B /\ A <> None)
(at level 70, no associativity).

Example notation: Some Dog =S= Dog /\ Some Dragon <S> Dog.
Proof. repeat split; simplify_eq. Qed.

(* A tactic for proving [in]equalities that use the notation above. *)
Ltac check_cards := match goal with
  | |- _ /\ _ => split; check_cards              (* split multiple [in]equalities *)
  | |- _ <S> _ => split; unfold not; simplify_eq (* handle both parts of <S> *)
  | |- _ =S= _ => reflexivity                    (* =S= is just simple equality *)
end.

(* Example of a goal this tactic can prove. *)
Example checking_cards: 
  Some Red =S= Red /\ Some Dog <S> Dragon /\ color Sonia =S= Blue /\ straight Sonia <S> 3.
Proof. check_cards. Qed.

(* Tactics for performing case analysis with respect to some funcion
   and filtering out cases that do not satisfy the assumptions.
   While verifying the solution to the puzzle, we will often want to
   find all players that satisfy some predicate. *)
   
(* Given an assumption H: f p, find all such p. *)
Ltac bruteforce p f := unfold f in * |-; destruct p; try discriminate.

(* Given an assumption H: pair p _, find all such p. *)
Ltac bruteforce_pairs p := unfold pair, known_pair in * |-; destruct p; try tauto.

(* Given an assumption H: finalist p, find all such p. *)
Ltac bruteforce_finalists p H := unfold finalist, place in * |-;
                                 destruct p;
                                 apply Nat.leb_le in H;
                                 simpl in H;
                                 try discriminate.

Example bruteforcing: 
  (forall p, color p =S= Blue -> straight p =S= 2) /\
  (forall p, pair p Sonia -> pair Sonia p) /\
  (forall p, finalist p -> place p < 3).
Proof.
  split.
  - intros.
    bruteforce p color.
    check_cards.
  - split; intros.
    + bruteforce_pairs p.
      unfold pair.
      tauto.
    + bruteforce_finalists p H; auto.
Qed.

(*** PROOFS FOR THE PUZZLE RULES ***)

(* Rule 1: Mateusz and Irena are paired, and they are neither 3rd nor 5th. *)
Fact rule1: pair Mateusz Irena /\ place Mateusz <> 3 /\ place Irena <> 5.
Proof.
  (* split conjunctions *)
  repeat split.
  (* prove Mateusz and Irena are a pair *)
  { 
    unfold pair, known_pair.
    tauto.
  }
  (* check if the places are correct *)
  all: simplify_eq.
Qed.

(* Rule 2.1: The straight of the only man in the final didn't start with 4. *)
Fact rule21: exists! p: Player, finalist p /\ man p /\ straight p <S> 4.
Proof.
  (* we wil show that this man is Hubert *)
  exists Hubert.
  unfold unique.
  split.
  (* prove that Hubert satisfies conditions *)
  - split.
    (* he is a finalist *)
    + unfold finalist, place.
      auto.
    + split.
      (* he is a man *)
      * now unfold man.
      (* his straight is not from 4 *)
      * check_cards.
  (* prove that nobody else does *)
  - intros x [F [M _]].
    (* brute-force all finalists *)
    bruteforce_finalists x F.
    (* filter out the women *)
    all: unfold man in M; try contradiction.
    (* the only player that's left is Hubert *)
    reflexivity.
Qed.

(* Rule 2.2: The straight of the owner of the Phoenix card didn't start with 4. *)
Fact rule22: forall p: Player, special p =S= Phoenix -> straight p <S> 4.
Proof.
  intros.
  (* filter out all players who do not have the Phoenix *)
  bruteforce p special.
  (* now just check the owner's straight *)
  check_cards.
Qed.

(* Rule 3: Natalia finished higher than Cezary and Sonia - higher than Tadeusz. *)
Fact rule3: place Natalia < place Cezary /\ place Sonia < place Tadeusz.
Proof.
  split; unfold place; auto.
Qed.

(* Rule 4: In the winning mixed pair it was Eliza who had the Mah Jong, and their straights were not blue. 
   As rule 4.1, we prove facts about the man. *)
Fact rule41: forall p: Player, pair p Eliza -> place p = 1 /\ man p /\ color p <S> Blue. 
Proof.
  intros.
  (* case analysis - find who is paired with Eliza *)
  bruteforce_pairs p.
  (* turns out it's Hubert, prove the facts about him *)
  repeat split; simplify_eq.
Qed.

(* As rule 4.2, we prove facts about Eliza. *)
Fact rule42: special Eliza =S= MahJong /\ color Eliza <S> Blue.
Proof.
  split; check_cards.
Qed.

(* Rule 5: The lowest straight was neither green nor red. *)
Fact rule5: forall p: Player, straight p =S= 2 -> color p <S> Green /\ color p <S> Red.
Proof.
  intros.
  (* case analysis: find who has the lowest straight *)
  bruteforce p straight.
  (* it's Sonia, let's prove her color is neither green nor red *)
  check_cards.
Qed.

(* Rule 6: Tadeusz was paired with a woman. Adam was paired with a man. *)
Fact rule6: forall p: Player, (pair Tadeusz p -> woman p) /\ (pair Adam p -> man p).
Proof.
  intro.
  (* find who is paired with them *)
  split; intro P; bruteforce_pairs p.
  (* for Tadeusz that's Natalia, so we can prove she's a woman *)
  unfold woman.
  tauto.
Qed. (* showing that Adam's pair was a man was trivial and Coq did it automatically *)

(* Rule 7.1: The highest straight was black. *)
Fact rule71: forall p: Player, straight p =S= 5 -> color p =S= Black.
Proof.
  intros.
  (* filter out players who do not have the highest straight *)
  bruteforce p straight.
  (* turns out its owner was Eliza *)
  check_cards.
Qed.

(* Rule 7.2: The person with the red straight had the Dog card. *)
Fact rule72: forall p: Player, color p =S= Red -> special p =S= Dog.
Proof.
  intros.
  (* try all players and discard those that don't have the red straight *)
  bruteforce p color.
  (* Hubert has it, prove he also has the Dog *)
  check_cards.
Qed.

(* Rule 7.3: Urszula was a runner-up and her straight was green. *)
Fact rule73: place Urszula = 2 /\ color Urszula =S= Green.
Proof.
  auto.
Qed.

(* Our solution is correct as all rules have been proven to hold *)

End Tichu.
