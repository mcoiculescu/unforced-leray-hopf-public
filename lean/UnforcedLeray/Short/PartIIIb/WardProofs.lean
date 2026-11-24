import UnforcedLeray.Short.PartIIIb.StatementsA
import UnforcedLeray.Short.PartIIIb.Compose

/-!
# Proofs for the Ward module (lines 4133-4332) that are short combinations

* `WardFields.shiftedResolvent` : `ward:shifted-resolvent` (4199-4201), from `R_{μ+1}D_{μ+1}=I`,
  `D_μ R_μ = I`, `D_{μ+1} = D_μ + I`.
* `WardFields.cutoffSource` : `ward:cutoff-source` (4203-4205).
* `hNilpotent_of_support` : `H² = 0` from `χ_o T = 0 → H T = 0` and `χ_o H T = 0` (4314-4319,
  5813-5814).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

namespace WardFields

variable {Vel Str : Type} [AddCommGroup Vel] [Module ℝ Vel] [AddCommGroup Str] [Module ℝ Str]
  (F : WardFields Vel Str)

theorem shiftedResolvent (h : F.IsFreeResolvent) : F.ShiftedResolvent := by
  obtain ⟨h1, -, h3, h4⟩ := h
  intro T
  set f : Vel := F.Pdiv (F.chiO T) with hf
  have hW : F.W T = -(F.Rmu f) := rfl
  have hW1 : F.W1 T = -(F.Rmu1 f) := rfl
  have hres : F.Rmu f - F.Rmu1 f = F.Rmu1 (F.Rmu f) := by
    have e : F.Dmu1 (F.Rmu f) = f + F.Rmu f := by
      simp [WardFields.Dmu1, h1]
    have h5 : F.Rmu1 (f + F.Rmu f) = F.Rmu1 f + F.Rmu1 (F.Rmu f) := map_add _ _ _
    have h6 : F.Rmu1 (F.Dmu1 (F.Rmu f)) = F.Rmu f := h4 _
    rw [e, h5] at h6
    rw [sub_eq_iff_eq_add, add_comm]
    exact h6.symm
  have hX0 : F.X0 T = F.Rmu1 (F.W T) := by
    have : F.X0 T = F.Rmu1 f - F.Rmu f := by
      simp only [WardFields.X0, hW, hW1]; abel
    rw [this, hW, map_neg, ← hres]; abel
  exact ⟨hX0, by rw [hX0]; exact h3 _⟩

theorem cutoffSource (h : F.IsFreeResolvent) : F.CutoffSource := by
  intro T
  have h2 := (F.shiftedResolvent h T).2
  simp only [WardFields.Y]
  rw [h2]; abel

end WardFields

/-- Old dependence in kernel form and young support give `H² = 0`
(source 4314-4319, 5813-5814). -/
theorem hNilpotent_of_support {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str)
    (hd : HOldKernel o chiO) (hs : HYoungSupport o chiO) : o.HNilpotent :=
  fun T => hd _ (hs T)

end UnforcedLeray.Short.PartIIIb
