import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs

/-!
# Off-axis identification of the physical field of `ĥ_A` (source 4991-4997, 5036-5039)

Off the axis, `Nv` of the `c`-periodic extension of `hhatChart` equals `Nv` of `hhatChart`
(periodicity of `ĥ_A` in `q`), which equals `Nv` of the ring profile, which is the stream lift
of `ρ ψ^p_A` by `ringStreamLift_components`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Every `q` differs from its centred-cell representative by an integer multiple of `c`. -/
theorem hhatn_cellRep_eq (ν q : ℝ) :
    ∃ n : ℤ, cellRep (cOf ν) q = q + (n : ℝ) * cOf ν :=
  ⟨-⌊(q + cOf ν / 2) / cOf ν⌋, by unfold cellRep; push_cast; ring⟩

/-- **Off-axis identification** (source 4991-4997, 5036-5039). -/
theorem hhatNvStream_proof (ν ε c : ℝ) (hε : 0 < ε) (χf : ℝ → ℝ) : HhatNvStream ν ε c χf := by
  intro hc hPer hRing A hJ τ y hy hd
  subst hc
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  -- periodic extension does not change the chart coefficient
  have hperExt : ∀ p : Chart,
      perExt (cOf ν) (hhatChart ν ε χf A) p = hhatChart ν ε χf A p := by
    rintro ⟨s, q, η⟩
    obtain ⟨n, hn⟩ := hhatn_cellRep_eq ν q
    have hp := hPer A s (q, η) n
    dsimp only at hp
    unfold perExt hhatChart
    rw [hn, hp]
  -- step 1: periodic extension is invisible to Nv
  have h1 : Nv ε⁻¹ (perExt (cOf ν) (hhatChart ν ε χf A)) τ y =
      Nv ε⁻¹ (hhatChart ν ε χf A) τ y := by
    unfold Nv
    rw [hperExt]
  -- step 2: the chart coefficient is the ring profile at the chart point
  have hp : 0 < (chart ε⁻¹ τ y).1 := age_pos hR.ne' hy
  have hRingPt : hhatChart ν ε χf A (chart ε⁻¹ τ y) =
      ringStreamProfile ε⁻¹ (psiRing ν χf A) (chart ε⁻¹ τ y) :=
    hRing A hJ (chart ε⁻¹ τ y) hp hd
  -- step 3: the ring lift is the stream lift
  have h3 : streamLift (ringStream ε⁻¹ τ (psiRing ν χf A)) y =
      Nv ε⁻¹ (ringStreamProfile ε⁻¹ (psiRing ν χf A)) τ y :=
    ringStreamLift_components hR hy hd
  rw [h1, h3]
  unfold Nv
  rw [hRingPt]

end UnforcedLeray.Short.PartIIIb.Concrete
