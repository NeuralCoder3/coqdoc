(* Xor ist nicht vordefiniert *)
(* Xor heißt: Eines wahr das andere falsch oder umgekehrt *)
Definition xor P Q :=
    (P /\ ~Q) \/ (~P /\ Q).
(* ~ steht für Negation ¬ *)
Notation "P 'xor' Q" := (xor P Q)(at level 80).

(* Ein paar Libraries, um unten Automatisation zu benutzen *)
Require Import PeanoNat.
Require Import Lia.
From Hammer Require Import Hammer.

Goal
    (forall x y z, 
        ((x<y xor x<>z)
        \/ 
        (x=y /\ x=z)) ->
        x > z
    ) ->
    forall x y, y>x.
Proof.
    intros H. (* →:Bew *)
    intros x y. (* ∀:Bew *)
    apply H with (y:=y). (* ∀:Anw und modus ponens (→:Anw) *)
      (* es sieht automatisch, dass ich für x y und für z x einsetze; nur y muss ich vorgeben *)
    
    destruct (Nat.eq_dec y x) as [H2|H2]. (* Fallunterscheidung über y=x *)
    (* Nat.eq_dec : forall n m : nat, n = m \/ n <> m *)
    - rewrite H2. (* subst ginge hier auch als Befehl. Subst Regel: ersetze y durch x *)
      right. (* \/:Bew *)
      split. (* /\:Bew *)
      + reflexivity. (* Subst, True, ... *)
      + reflexivity. 
    - left. (* \/:Bew *)
      right. (* Subst, \/:Bew *)
      split. (* /\:Bew *)
      + apply Nat.lt_irrefl. (* Lemma Nat.lt_irrefl : forall x : nat, ~ x < x *)
      + apply H2.
      (* Fertig *)
Restart. (* Beweis mit Taktiken *)
    intros H x y.
    apply H with (y:=y).
    destruct (Nat.eq_dec y x).
    - lia. (* lia löst "rechnen" *)
    - left. right. lia. (* hier braucht es ein wenig Hilfe *)
    (* Fertig *)
Restart. (* Beweis mit Taktiken *)
    now sfirstorder. (* fertig. Automatisation hat es gelöst *)
    (* Fertig *)
Qed.
