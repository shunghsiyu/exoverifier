/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-- Like `Decidable` but with an "unknown" value. Useful when we don't care about completeness. -/
inductive Semidecision (P : Prop) : Type where
  | isTrue  :  P → Semidecision P
  | isFalse : ¬P → Semidecision P
  | unknown  :      Semidecision P

namespace Semidecision

variable {P Q : Prop}

instance : Inhabited (Semidecision P) := ⟨unknown⟩

protected def repr : Semidecision P → String
  | isTrue _  => "isTrue"
  | isFalse _ => "isFalse"
  | unknown   => "unknown"

instance : Repr (Semidecision P) := ⟨fun s _ => Semidecision.repr s⟩

def ofDecidable (P : Prop) [h : Decidable P] : Semidecision P :=
  match h with
  | .isTrue h  => isTrue h
  | .isFalse h => isFalse h

/-- Convert semidecision to `true` iff P is definitely true. -/
def toBool : Semidecision P → Bool
  | isTrue _ => true
  | _        => false

def asTrue : Semidecision P → Prop
  | isTrue _ => True
  | _        => False

theorem ofAsTrue : ∀ (x : Semidecision P), asTrue x → P
  | isTrue h,  _ => h
  | isFalse _, h => False.elim h
  | unknown,   h => False.elim h

def asFalse : Semidecision P → Prop
  | isFalse _ => True
  | _         => False

theorem notOfAsFalse : ∀ (x : Semidecision P), asFalse x → ¬P
  | isTrue _,  h => False.elim h
  | isFalse h, _ => h
  | unknown,   h => False.elim h

def negate : Semidecision P → Semidecision ¬P
  | isTrue p  => isFalse (fun np => np p)
  | isFalse p => isTrue p
  | unknown   => unknown

/-- Sequence two semidecisions, using the first one first. -/
def orelse : Semidecision P → Semidecision P → Semidecision P
  | isTrue p,  _ => isTrue p
  | isFalse p, _ => isFalse p
  | _,         x => x

def bindCases : Semidecision P → (P → Semidecision Q) → (¬P → Semidecision Q) → Semidecision Q
  | isTrue p,  t, _ => t p
  | isFalse p, _, f => f p
  | _,         _, _ => unknown

/-- `bind` for semidecisions. -/
def bindTrue : Semidecision P → (P → Semidecision Q) → Semidecision Q :=
  fun p t => bindCases p t (fun _ => unknown)

/-- Like bind, but takes a function of the negation of P. -/
def bindFalse : Semidecision P → (¬P → Semidecision Q) → Semidecision Q :=
  fun p f => bindCases p (fun _ => unknown) f

/-- Convert a semidecision to a weaker semidecision using modus ponens. -/
def modusPonens : Semidecision P → (P → Q) → Semidecision Q :=
  fun p h => p.bindTrue (isTrue ∘ h)

/-- Convert a semidecision to a stronger semidecision using modus tollens. -/
def modusTollens : Semidecision Q → (P → Q) → Semidecision P :=
  fun p h => p.bindFalse (fun nq => isFalse (nq ∘ h))

/-- `Procedure L ω` is a procedure that semidecides, for a given x, whether x ∈ L
    using values of type ω as witnesses. -/
abbrev Procedure {α : Type _} (L : α → Prop) (ω : Type _) : Type _ :=
  ∀ (x : α), ω → Semidecision (L x)

namespace Procedure

variable {α ω ω₁ ω₂ : Type _}
variable {L L₁ L₂ : α → Prop}

/-- R is sound w.r.t. L when, for any x, if there exists a w s.t. R x w then x ∈ L. -/
abbrev sound (L : α → Prop) (R : α → ω → Prop) : Prop :=
  ∀ x w, R x w → L x

/-- Make a decision procedure by showing the soundness of a decidable relation R : α → ω → Prop
    w.r.t. the language L. -/
def ofDecidableSoundRelation {L : α → Prop} (R : α → ω → Prop) [∀ x w, Decidable (R x w)] (s : sound L R) : Procedure L ω :=
  fun x w => (ofDecidable _).modusPonens (s x w)

/-- Make a complete decision procedure for the language if the language is decidable. -/
def ofDecidableLanguage [DecidablePred L] : Procedure L ω :=
  fun _ _ => ofDecidable _

def ofSubsetProcedure (f : Procedure L₁ ω) (h : ∀ x, L₁ x → L₂ x) : Procedure L₂ ω :=
  fun x w => (f x w).modusPonens (h x)

/-- Sequence two decision procedures. -/
def sequence (f : Procedure L ω) (g : Procedure L ω) : Procedure L ω :=
  fun x w => (f x w).orelse (g x w)

/-- Sequence two decision procedures with two (potentially different) witnesses. -/
def sequence' (f : Procedure L ω₁) (g : Procedure L ω₂) : Procedure L (ω₁ × ω₂) :=
  fun x w => (f x w.1).orelse (g x w.2)

/-- Conditionally choose a decision procedure based on which witness is present. -/
def split (f : Procedure L ω₁) (g : Procedure L ω₂) : Procedure L (ω₁ ⊕ ω₂) :=
  fun x w =>
    match w with
    | .inl w₁ => f x w₁
    | .inr w₂ => g x w₂

/-- A trivial decision procedure that rejects everything. -/
def trivial : Procedure L ω :=
  fun _ _ => unknown

end Procedure
end Semidecision
