import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_481

namespace PEqualNP.Outside.L_lib_604

theorem z2_cases : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide

theorem z2_add_self : ∀ u : ZMod 2, u + u = 0 := by decide

theorem contra_of_not_ok {n m : ℕ} (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2)
    (S : Finset (Fin m))
    (h : ¬ ∃ x : Fin n → ZMod 2, ∀ e ∈ S, (∑ j, row e j * x j) = rhs e) :
    ∃ I : Finset (Fin m), I ⊆ S ∧ (∀ j : Fin n, I.sum (fun e => row e j) = 0) ∧
      I.sum rhs = 1 := by
  let A : Matrix (Fin m) (Fin n) (ZMod 2) := fun i j => if i ∈ S then row i j else 0
  let b : Fin m → ZMod 2 := fun i => if i ∈ S then rhs i else 0
  have hA : ¬ ∃ x : Fin n → ZMod 2, A.mulVec x = b := by
    rintro ⟨x, hx⟩
    apply h
    refine ⟨x, fun e he => ?_⟩
    have := congrFun hx e
    simpa [A, b, Matrix.mulVec, dotProduct, he] using this
  obtain ⟨y, hy0, hy1⟩ := (PEqualNP.Outside.L_lib_481 m n A b).mp hA
  refine ⟨Finset.univ.filter (fun i => i ∈ S ∧ y i ≠ 0), ?_, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.1
  · intro j
    have := congrFun hy0 j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    by_cases hS : i ∈ S <;> rcases z2_cases (y i) with hy | hy <;> simp [A, hS, hy]
  · simp only [dotProduct] at hy1
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hy1
    by_cases hS : i ∈ S <;> rcases z2_cases (y i) with hy | hy <;> simp [b, hS, hy]

theorem sum_symmDiff_z2 {m : ℕ} (A B : Finset (Fin m)) (f : Fin m → ZMod 2) :
    (symmDiff A B).sum f = A.sum f + B.sum f := by
  have key : ∀ s : Finset (Fin m), s.sum f = ∑ i, if i ∈ s then f i else 0 := by
    intro s
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [key, key A, key B, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [Finset.mem_symmDiff, hA, hB, z2_add_self]

theorem main {n m : ℕ} (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2)
    (W : Finset (Finset (Fin m)))
    (hW : ∀ I, I ∈ W ↔ (∀ j : Fin n, I.sum (fun e => row e j) = 0) ∧ I.sum rhs = 1)
    (h0 : ¬ ∃ x : Fin n → ZMod 2, ∀ e ∈ (Finset.univ : Finset (Fin m)),
      (∑ j, row e j * x j) = rhs e)
    (h1 : ∀ e : Fin m, ¬ ∃ x : Fin n → ZMod 2, ∀ e' ∈ Finset.univ.erase e,
      (∑ j, row e' j * x j) = rhs e') :
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  have hne : W.Nonempty := by
    obtain ⟨I, _, hI1, hI2⟩ := contra_of_not_ok row rhs Finset.univ h0
    exact ⟨I, (hW I).mpr ⟨hI1, hI2⟩⟩
  have half : ∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card := by
    intro e he
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp he
    obtain ⟨D, hDsub, hD1, hD2⟩ := contra_of_not_ok row rhs _ (h1 e)
    have heD : e ∉ D := fun h => by simpa using hDsub h
    have hC' := (hW C).mp hC
    let Δ := symmDiff C D
    have heΔ : e ∈ Δ := Finset.mem_symmDiff.mpr (Or.inl ⟨heC, heD⟩)
    have hΔrow : ∀ j : Fin n, Δ.sum (fun e => row e j) = 0 := by
      intro j
      rw [sum_symmDiff_z2, hC'.1 j, hD1 j, add_zero]
    have hΔrhs : Δ.sum rhs = 0 := by
      rw [sum_symmDiff_z2, hC'.2, hD2]; decide
    have tW : ∀ I ∈ W, symmDiff I Δ ∈ W := by
      intro I hI
      have hI' := (hW I).mp hI
      refine (hW _).mpr ⟨fun j => ?_, ?_⟩
      · rw [sum_symmDiff_z2, hI'.1 j, hΔrow j, add_zero]
      · rw [sum_symmDiff_z2, hI'.2, hΔrhs, add_zero]
    have tmem : ∀ I : Finset (Fin m), e ∈ symmDiff I Δ ↔ e ∉ I := by
      intro I
      rw [Finset.mem_symmDiff]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact absurd heΔ h
        · exact h
      · intro h; exact Or.inr ⟨heΔ, h⟩
    have hcard : (W.filter (fun subset => e ∈ subset)).card =
        (W.filter (fun subset => ¬ e ∈ subset)).card := by
      apply Finset.card_nbij' (fun I => symmDiff I Δ) (fun I => symmDiff I Δ)
      · intro I hI
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hI ⊢
        exact ⟨tW I hI.1, fun h => (tmem I).mp h hI.2⟩
      · intro I hI
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hI ⊢
        exact ⟨tW I hI.1, (tmem I).mpr hI.2⟩
      · intro I _
        show symmDiff (symmDiff I Δ) Δ = I
        rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
      · intro I _
        show symmDiff (symmDiff I Δ) Δ = I
        rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := W) (fun subset => e ∈ subset)
    omega
  have avg : ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w := by
    intro w
    have step : ∀ I ∈ W, I.sum w = ∑ e ∈ W.biUnion id, if e ∈ I then w e else 0 := by
      intro I hI
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (show I ⊆ W.biUnion id from Finset.subset_biUnion_of_mem id hI)]
    rw [Finset.sum_congr rfl step, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, ← mul_assoc, half e he]
  refine ⟨hne, half, fun w => ⟨avg w, ?_⟩⟩
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hlt := Finset.sum_lt_sum_of_nonempty hne hcon
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, avg w] at hlt
  exact lt_irrefl _ hlt

end PEqualNP.Outside.L_lib_604

theorem PEqualNP.Outside.L_lib_604 : ∀ (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2),
  let ok := fun (rows : Finset (Fin m)) => ∃ x : Fin n → ZMod 2,
    ∀ e ∈ rows, (∑ j, row e j * x j) = rhs e
  let W := Finset.univ.filter (fun indices : Finset (Fin m) =>
    (∀ j : Fin n, indices.sum (fun e => row e j) = 0) ∧ indices.sum rhs = 1)
  ¬ ok Finset.univ → (∀ e : Fin m, ¬ ok (Finset.univ.erase e)) →
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  intro n m row rhs ok W h0 h1
  exact PEqualNP.Outside.L_lib_604.main row rhs W (fun I => by simp [W]) h0 h1
