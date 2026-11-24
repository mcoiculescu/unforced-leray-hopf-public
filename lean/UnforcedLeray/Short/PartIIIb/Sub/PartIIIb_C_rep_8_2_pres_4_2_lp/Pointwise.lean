import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RawSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.ChartRuleGen

/-!
# Piece 6: the pointwise splitting of the coefficient change
(`PartIII-b:C/rep/8/2/pres/4/2/lp/6`)

Source `the November 2 reference manuscript`
5287-5289.  At a chart point (off the axis) `U = U_raw + E_εα + r_b` with all three summands
`C²` at the point, so the first and second derivatives split and the change density of `(U, U_raw)`
is at most the sum of the densities of `E_εα` and `r_b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PwSplit

theorem da {f : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y) : DifferentiableAt ℝ f y :=
  hf.differentiableAt (by norm_num)

theorem pd_add {f g : Space → Space} {y : Space} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (j : Fin 3) :
    physPd (fun z => f z + g z) j y = physPd f j y + physPd g j y := by
  unfold physPd
  rw [show (fun z => f z + g z) = f + g from rfl, (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  rfl

theorem pd_diff {f : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y) (l : Fin 3) :
    DifferentiableAt ℝ (fun z => physPd f l z) y := by
  unfold physPd
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : ContDiffAt ℝ 1 (fun z => fderiv ℝ f z (coordinateVector l)) y :=
    h1.clm_apply contDiffAt_const
  exact h2.differentiableAt one_ne_zero

theorem pd2_add {f g : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) (j l : Fin 3) :
    physPd2 (fun z => f z + g z) j l y = physPd2 f j l y + physPd2 g j l y := by
  unfold physPd2
  have hev : (fun y' => physPd (fun z => f z + g z) l y') =ᶠ[𝓝 y]
      fun y' => physPd f l y' + physPd g l y' := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y' h1 h2
    exact pd_add (da h1) (da h2) l
  show fderiv ℝ (fun y' => physPd (fun z => f z + g z) l y') y (coordinateVector j) = _
  rw [hev.fderiv_eq]
  exact pd_add (pd_diff hf l) (pd_diff hg l) j

theorem physPd_zero' (j : Fin 3) (y : Space) : physPd (0 : Space → Space) j y = 0 := by
  unfold physPd
  simp

theorem physPd2_zero' (j l : Fin 3) (y : Space) : physPd2 (0 : Space → Space) j l y = 0 := by
  unfold physPd2
  have : (fun y' => physPd (0 : Space → Space) l y') = 0 := by
    funext y'; exact physPd_zero' l y'
  rw [this]
  exact physPd_zero' j y

/-- The pointwise splitting at one point, for two `C²` summands. -/
theorem split_le {f g : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) :
    coefChgDens (fun z => f z + g z) f y ≤ coefChgDens g 0 y := by
  have e1 : fderiv ℝ (fun z => f z + g z) y - fderiv ℝ f y = fderiv ℝ g y := by
    rw [show (fun z => f z + g z) = f + g from rfl, (( da hf).hasFDerivAt.add (da hg).hasFDerivAt).fderiv]
    abel
  have e2 : ∀ j l, physPd2 (fun z => f z + g z) j l y - physPd2 f j l y = physPd2 g j l y := by
    intro j l
    rw [pd2_add hf hg j l]
    abel
  have e3 : secondJet (fun z => f z + g z) y - secondJet f y = secondJet g y := by
    unfold secondJet
    rw [jet2_sub]
    simp only [e2]
  unfold coefChgDens
  have e4 : f y + g y - f y = g y := by abel
  have e5 : fderiv ℝ (0 : Space → Space) y = 0 := by simp
  have e6 : secondJet g y - 0 = secondJet g y := by
    ext a b : 2
    simp
  simp only [Pi.zero_apply, sub_zero, e1, e3, e4, e5, secondJet_zero, e6, le_refl]

end PwSplit

theorem coefChgPointwise (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    CoefChgPointwise D := by
  unfold CoefChgPointwise
  have hlim : Tendsto (retNu D.Pl D.σ₀) atTop (nhds 0) := retNu_tendsto D.σ₀ hst.omega_ne
  filter_upwards [hst.actual, hlim.eventually (gt_mem_nhds zero_lt_one)] with n hact hn
  intro p hp
  set L := D.level n with hL
  set q := L.params D.Pl with hq
  set τ := NearInst.chartTau L.ε⁻¹ p with hτ
  set y := NearInst.chartY L.ε⁻¹ p with hy
  have hεpos : 0 < L.ε := L.ε_pos
  have hyax : y ∉ axis := crg_chartY_not_mem_axis (inv_pos.2 hεpos) hp
  obtain ⟨z, -, hV, -, -⟩ := hact.split.state
  set α : Fin 2 → ℝ := fun i => (q.coord z i) with hαdef
  have hVα : ∀ τ y, D.V n τ y = rawU D.Pl L τ y + entrOf q α τ y := fun τ y => hV τ y
  have slice : ∀ F : ℝ × Space → Space, ContDiffAt ℝ 2 F (τ, y) →
      ContDiffAt ℝ 2 (fun z : Space => F (τ, z)) y := fun F hF =>
    hF.comp y (contDiffAt_const.prodMk contDiffAt_id)
  -- the exact background
  have hUs : ContDiffAt ℝ 2 (L.U τ) y := by
    have h := hact.profile.smoothU
    have h2 : ContDiff ℝ 2 fun x : ℝ × Space => L.U x.1 x.2 := h.of_le (by norm_num)
    exact slice _ h2.contDiffAt
  -- the raw coefficient
  have hraw : ContDiffAt ℝ 2 (rawU D.Pl L τ) y := by
    have hψ : ContDiffOn ℝ 3 (fun x : ℝ × UnforcedLeray.Cyl.Plane => q.train.ψ x.1 x.2)
        (Ioi 0 ×ˢ univ) :=
      L.train_stream_smooth.of_le (by norm_num)
    have h := PwSplitRaw.rawU_contDiffOn_offAxis_of q hεpos hψ
    have hopen : IsOpen PwSplitRaw.offAxis := PwSplitRaw.isOpen_offAxis
    exact slice _ (h.contDiffAt (hopen.mem_nhds hyax))
  -- the entrance field
  have hent : ContDiffAt ℝ 2 (entrOf q α τ) y := by
    have hI : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => q.inlet i x.1 x.2) := fun i =>
      inlet_contDiff_joint D.Pl.eigenvalue D.Pl.mode hst.planar.eigenpair hact.regime
        (le_of_lt hn) rfl i
    have hsum : ContDiff ℝ 2 (fun x : ℝ × Space => entrOf q α x.1 x.2) := by
      have : (fun x : ℝ × Space => entrOf q α x.1 x.2) =
          fun x => ∑ i : Fin 2, α i • q.inlet i x.1 x.2 := rfl
      rw [this]
      exact ContDiff.sum fun i _ => ((hI i).of_le (by norm_num)).const_smul _
    exact slice _ hsum.contDiffAt
  have hVs : ContDiffAt ℝ 2 (D.V n τ) y := by
    have : D.V n τ = fun z => rawU D.Pl L τ z + entrOf q α τ z := funext (hVα τ)
    rw [this]; exact hraw.add hent
  have hrbeq : D.rb n τ = fun z => L.U τ z - D.V n τ z := by
    funext z
    have h1 : L.U τ z = D.V n τ z + D.rb n τ z := rfl
    rw [h1]; abel
  have hrb : ContDiffAt ℝ 2 (D.rb n τ) y := by
    rw [hrbeq]; exact hUs.sub hVs
  have hUeq : L.U τ = fun z => D.V n τ z + D.rb n τ z := rfl
  show coefChgDens (L.U τ) (D.V n τ) y ≤ coefChgDens (D.rb n τ) 0 y
  rw [hUeq]
  exact PwSplit.split_le hVs hrb

end UnforcedLeray.Short.PartIIIb.Concrete
