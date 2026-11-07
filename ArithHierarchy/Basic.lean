import Mathlib.Computability.Halting

open Nat.Partrec

namespace AH

/- We use a mutual definition to define Σ_n and Π_n classes in terms of eachother-/
mutual
  def Sigma : ℕ → (ℕ → Prop) → Prop
    | 0, p => ComputablePred p
    | n + 1, p => ∃ q, Pi n q ∧ ∀ x, p x ↔ ∃ y, q (Nat.pair x y)
  def Pi : ℕ → (ℕ → Prop) → Prop
    | 0, p => ComputablePred p
    | n + 1, p => ∃ q, Sigma n q ∧ ∀ x, p x ↔ ∀ y, q (Nat.pair x y)
end

def haltSet : ℕ → Prop :=
  fun n => (Code.eval (Denumerable.ofNat Code n) n).Dom


section Basic
variable {n : ℕ} {p : ℕ → Prop}

theorem sigma_zero_iff : Sigma 0 p ↔ ComputablePred p := by
  constructor
  · intro P
    obtain⟨a, b⟩ := P
    exact Computable.computablePred b
  · exact id

theorem pi_zero_iff : Pi 0 p ↔ ComputablePred p := by
  constructor
  · intro P
    obtain⟨a, b⟩ := P
    exact Computable.computablePred b
  · exact id

theorem pi_succ_iff :
    Pi (n + 1) p ↔ ∃ q : ℕ → Prop, Sigma n q ∧ ∀ x, p x ↔ ∀ y, q (Nat.pair x y) := by
  constructor
  · intro P
    exact Set.exists_mem_ofPred.mp P
  · exact id

lemma not_not : ComputablePred p ↔ ComputablePred fun a => ¬¬p a := by simp

theorem sigma_iff_pi_not : (∀ p, Sigma n p ↔ Pi n (fun x => ¬ p x)):= by
  induction n with
  | zero =>
    intro p
    rw [pi_zero_iff, sigma_zero_iff]
    exact ⟨ComputablePred.not, fun P => by simpa using ComputablePred.not P⟩
  | succ n ih =>
    intro p
    simp only[Pi, Sigma]
    constructor
    · intro S
      obtain⟨q, hq, hp⟩ := S
      refine ⟨fun z => ¬ q z, ?_, ?_⟩
      · specialize ih fun z => ¬ q z
        obtain⟨a, b⟩ := ih
        apply b
        simp only [Classical.not_not]
        exact hq
      · intro x
        rw[hp, not_exists]
    · intro S
      obtain⟨q, hq, hp⟩ := S
      refine ⟨fun z => ¬ q z, ?_, ?_⟩
      · exact (ih q).1 hq
      · intro x
        specialize hp x
        rw[←not_iff_not]
        push Not
        exact iff_comm.mp (id (Iff.symm hp))

theorem pi_iff_sigma_not : (∀ p, Pi n p ↔ Sigma n (fun x => ¬ p x)):= by
  intro p
  rw [sigma_iff_pi_not (fun x => ¬ p x)]
  simp only [Classical.not_not]

theorem sigma_congr {q : ℕ → Prop} (h : ∀ x, p x ↔ q x) : Sigma n p ↔ Sigma n q := by
  simp only [← eq_iff_iff, ← funext_iff] at h
  exact Eq.to_iff (congrArg (Sigma n) h)

theorem pi_congr {q : ℕ → Prop} (h : ∀ x, p x ↔ q x) : Pi n p ↔ Pi n q := by
  simp only [← eq_iff_iff, ← funext_iff] at h
  exact Eq.to_iff (congrArg (Pi n) h)


theorem sigma_comp {f : ℕ → ℕ} (hf : Computable f) :
    Sigma n p → Sigma n (fun x => p (f x)) := by
  sorry

theorem pi_comp {f : ℕ → ℕ} (hf : Computable f) :
    Pi n p → Pi n (fun x => p (f x)) := by
  sorry

theorem sigma_succ_of_sigma : Sigma n p → Sigma (n + 1) p := by
  induction n generalizing p with
  | zero =>
    rw [zero_add]
    intro h
    rw [sigma_zero_iff, ComputablePred.computable_iff] at h
    obtain ⟨f, hf, rfl⟩ := h
    refine ⟨fun z => f (Nat.unpair z).1 = true, ?_, ?_⟩
    · rw [pi_zero_iff, ComputablePred.computable_iff]
      exact ⟨fun z => f (Nat.unpair z).1, hf.comp (Computable.fst.comp Computable.unpair), rfl⟩
    · intro x
      simp
  | succ n ih =>
    intro h
    obtain ⟨q, hq, hp⟩ := h
    refine ⟨q, ?_, hp⟩
    rw[pi_iff_sigma_not] at *
    exact ih hq

theorem pi_succ_of_pi : Pi n p → Pi (n + 1) p := by
  intro h
  rw[pi_iff_sigma_not] at *
  exact sigma_succ_of_sigma h

theorem pi_succ_of_sigma : Sigma n p → Pi (n + 1) p := by
  intro h
  refine ⟨fun z => p (Nat.unpair z).1, ?_, ?_⟩
  · sorry
  · intro x
    simp



theorem sigma_succ_of_pi : Pi n p → Sigma (n + 1) p := by
  intro h
  rw[pi_iff_sigma_not] at *
  have := pi_succ_of_sigma h
  rw [← sigma_iff_pi_not] at this
  exact this



end Basic


section Closure
variable {n : ℕ} {p q : ℕ → Prop}

theorem sigma_and : Sigma n p → Sigma n q → Sigma n (fun x => p x ∧ q x) := by
  sorry

theorem sigma_or : Sigma n p → Sigma n q → Sigma n (fun x => p x ∨ q x) := by
  sorry

theorem pi_and : Pi n p → Pi n q → Pi n (fun x => p x ∧ q x) := by
  sorry

theorem pi_or : Pi n p → Pi n q → Pi n (fun x => p x ∨ q x) := by
  sorry


end Closure


end AH
