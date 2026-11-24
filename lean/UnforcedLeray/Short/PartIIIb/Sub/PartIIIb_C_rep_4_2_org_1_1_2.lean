import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq

/-!
# `PartIII-b:C/rep/4/2/org/1/1/2`: `SepWeakExistenceThin` from the weak stress inverse

Source `the November 2 reference manuscript`
3596-3621 (`sep:kernel`, `sep:resolvent`: `W_μ = -S_μT`), 4145, 4155-4171, 1556-1572, 5573-5576.

The global weak solution of `D_μ w = ℙ div 𝒩_T(oldThin T)` is `S (oldThin T)`, with `S` the weak
stress inverse of the level (`IsWeakStressInverse`, `Level.lean` 223).  Two source facts remain:

* `SepInvExists`: the weak stress inverse exists at the large levels of a `RepairStanding`
  sequence (4145, 1675-1690; `seqStressInverse_of` from `StressTransportExists`,
  `StressMapWeakSol`, `StressPairAE`);
* `SepInvYoung`: its value on a thin old source is the separated-kernel response `-W_μ` at
  `bodyMeasure`-a.e. young chart point (3611-3621, 4155-4171; absolute convergence of the
  kernel integral on `r ≥ R√ν` by `IIIa.sepKernelBounds` and the finite old mass 5573-5576).

`sepWeakExistenceThin_of` is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Existence of the weak stress inverse along the sequence** (source 4145, 1556-1572,
1675-1690, 3888-3890): for large `n` and every `z ∈ [-1,1]` there is a continuous linear
`S : Z → H` all of whose values are weakly solenoidal distributional `Y_2` solutions of
`D_μ w = ℙ div 𝒩_T(T₁+T₂)`. -/
def SepInvExists (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∃ S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
      IsWeakStressInverse S (D.level n).ε (D.mu n z)

/-- **The weak stress inverse of a thin old source is the separated-kernel response on the young
region** (source 3596-3621 `sep:kernel`, `sep:resolvent`; 4155-4171; 5573-5576): for every weak
stress inverse `S`, old thin source `oldThin T` with chart representatives `g₁ g₂`, the coefficient
of `S (oldThin T)` is `-coefOf (wardW …(g₁+g₂)) = -W_μ` at `bodyMeasure`-a.e. young chart point
`ν s ≤ 1`. -/
def SepInvYoung (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
      IsWeakStressInverse S (D.level n).ε (D.mu n z) →
      ∀ (T : LStr D.Pl D.K (D.level n)) (g₁ g₂ : Chart → Ten3),
        IsRep D.Pl D.K (D.level n) (oldThin D.Pl D.K (D.level n) T) g₁ g₂ →
        ∀ᵐ p ∂(bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν),
          (D.level n).ν * p.1 ≤ 1 →
            ((S (oldThin D.Pl D.K (D.level n) T) : LVel D.Pl (D.level n)) : Chart → Merid) p =
              -coefOf (D.level n).ε⁻¹ (wardW (D.level n).ν (D.mu n z) (D.level n).ε⁻¹
                (cOf (D.level n).ν) (g₁ + g₂)) p

/-- **`SepWeakExistenceThin` from the weak stress inverse and its young-region value.** -/
theorem sepWeakExistenceThin_of {dm dp : ℝ} (hE : SepInvExists dm dp) (hY : SepInvYoung dm dp) :
    SepWeakExistenceThin dm dp := by
  intro D hst
  filter_upwards [hE D hst, hY D hst] with n h1 h2 z hz
  obtain ⟨S, hS⟩ := h1 z hz
  intro T g₁ g₂ hg
  exact ⟨S (oldThin D.Pl D.K (D.level n) T), hS _, h2 z hz S hS T g₁ g₂ hg⟩

end UnforcedLeray.Short.PartIIIb.Concrete
