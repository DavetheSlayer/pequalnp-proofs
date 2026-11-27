import PEqualNP.Defs
import Mathlib.Data.FinEnum

namespace PEqualNP.Outside.L_meta_25499

theorem setWidth_xor_aux {k b : ℕ} (x d : BitVec k) :
    (x ^^^ d).setWidth b = x.setWidth b ^^^ d.setWidth b := by
  ext i hi
  simp

theorem xor_xor_cancel_aux {k : ℕ} (x d : BitVec k) : x ^^^ d ^^^ d = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem natAbs_sum_le_aux {ι : Type} (S : Finset ι) (g : ι → ℤ) :
    (S.sum g).natAbs ≤ S.sum (fun i => (g i).natAbs) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

end PEqualNP.Outside.L_meta_25499

theorem PEqualNP.Outside.L_meta_25499 : ∀ (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b),
  let slice := fun label : BitVec b =>
    Finset.univ.filter (fun key : BitVec k => key.setWidth b = label)
  let bias := fun t : BitVec b =>
    (slice t).sum (fun word => if f word then (-1 : ℤ) else 1)
  let agreements := (slice s).filter (fun x => f x = f (x ^^^ d))
  (bias s + bias (s ^^^ d.setWidth b)).natAbs ≤ 2 * agreements.card := by
  intro k b f d s slice bias agreements
  have h2 : bias (s ^^^ d.setWidth b) =
      (slice s).sum (fun x => if f (x ^^^ d) then (-1 : ℤ) else 1) := by
    show (slice (s ^^^ d.setWidth b)).sum _ = _
    symm
    refine Finset.sum_nbij' (fun x => x ^^^ d) (fun x => x ^^^ d) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [PEqualNP.Outside.L_meta_25499.setWidth_xor_aux, hx]
    · intro x hx
      simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [PEqualNP.Outside.L_meta_25499.setWidth_xor_aux, hx,
        PEqualNP.Outside.L_meta_25499.xor_xor_cancel_aux]
    · intro x _
      exact PEqualNP.Outside.L_meta_25499.xor_xor_cancel_aux x d
    · intro x _
      exact PEqualNP.Outside.L_meta_25499.xor_xor_cancel_aux x d
    · intro x _
      rfl
  have hb : bias s + bias (s ^^^ d.setWidth b) = (slice s).sum
      (fun x => (if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)) := by
    rw [h2, Finset.sum_add_distrib]
  rw [hb]
  refine (PEqualNP.Outside.L_meta_25499.natAbs_sum_le_aux _ _).trans ?_
  show _ ≤ 2 * ((slice s).filter (fun x => f x = f (x ^^^ d))).card
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  cases f x <;> cases f (x ^^^ d) <;> simp
