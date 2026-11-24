import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Cutoff
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part II-b, task `PartII-b:T22/2/2/3`: the Laplacian integration by parts (`RtdLapIBP`)

Source of record: `the November 2 reference manuscript`, lines 2097-2101 (weight
one). Only `Δg`, not `∂_q² g`, is known to decay, so the identity is proved with the `η`-cut-off
`χ_R = cutF R`: with `q1 = χ(η)(∂_q g · h - g · ∂_q h)` and `e2 = χ(η)(∂_η g · h - g · ∂_η h)`,

  `∂_q q1 + ∂_η e2 = χ(η)(Δg · h - g · Δh) + cutD(η)(∂_η g · h - g · ∂_η h)`.

The `q`-flux integrates to zero by `q`-periodicity, the `η`-flux by compact support. Letting
`R = n + 1 → ∞` (dominated convergence on the left, `|cutD| ≤ K/R` on the right) gives
`∫ (Δg · h - g · Δh) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

namespace RtdLapAux

theorem cell_eq (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem abs_mul_le_of_decay {a b C D J : ℝ} (hJ : 0 < J) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (ha : |a| * J ^ (2 : ℝ) ≤ C) (hb : |b| * J ^ (2 : ℝ) ≤ D) :
    |a| * |b| ≤ C * D * J ^ (-4 : ℝ) := by
  have key : J ^ (2 : ℝ) * J ^ (2 : ℝ) * J ^ (-4 : ℝ) = 1 := by
    rw [← Real.rpow_add hJ, ← Real.rpow_add hJ]
    norm_num
  have hprod : (|a| * J ^ (2 : ℝ)) * (|b| * J ^ (2 : ℝ)) ≤ C * D :=
    mul_le_mul ha hb (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hJ.le _)) hC0
  have hJ4 : 0 ≤ J ^ (-4 : ℝ) := Real.rpow_nonneg hJ.le _
  calc |a| * |b| = (|a| * J ^ (2 : ℝ)) * (|b| * J ^ (2 : ℝ)) * J ^ (-4 : ℝ) := by
        linear_combination (-(|a| * |b|)) * key
    _ ≤ C * D * J ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right hprod hJ4

/-- On the strip `|q| ≤ c/2` the four decay quantities of `g` are `O(jb^{-2})`. -/
theorem strip_bounds {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |g x| * B0579.jb x ^ (2 : ℝ) ≤ C ∧ |B0579.pd 0 g x| * B0579.jb x ^ (2 : ℝ) ≤ C ∧
      |B0579.pd 1 g x| * B0579.jb x ^ (2 : ℝ) ≤ C ∧ |lapP g x| * B0579.jb x ^ (2 : ℝ) ≤ C := by
  obtain ⟨C, hC⟩ := hg.cell_decay 2
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hp : 0 ≤ B0579.jb x ^ (2 : ℝ) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have key : (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ (2 : ℝ)
      ≤ max C 0 := (hC x hx).trans (le_max_left C 0)
  have h0 := abs_nonneg (g x)
  have h1 := abs_nonneg (B0579.pd 0 g x)
  have h2 := abs_nonneg (B0579.pd 1 g x)
  have h3 := abs_nonneg (lapP g x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : |g x| * B0579.jb x ^ (2 : ℝ) ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key
  · have e : |B0579.pd 0 g x| * B0579.jb x ^ (2 : ℝ) ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key
  · have e : |B0579.pd 1 g x| * B0579.jb x ^ (2 : ℝ) ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key
  · have e : |lapP g x| * B0579.jb x ^ (2 : ℝ) ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key

/-- A product of two continuous functions with the strip decay bounds is integrable on the cell. -/
theorem integrable_mul_strip {c : ℝ} {a b : B0579.Plane → ℝ} (ha : Continuous a)
    (hb : Continuous b) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (ha' : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → |a x| * B0579.jb x ^ (2 : ℝ) ≤ A)
    (hb' : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → |b x| * B0579.jb x ^ (2 : ℝ) ≤ B) :
    IntegrableOn (fun x => a x * b x) (UnforcedLeray.Cyl.cell c) := by
  refine TransportIBP.integrableOn_cell_of_bound
    (Q := fun x => A * B * B0579.jb x ^ (-4 : ℝ))
    (TransportIBP.integrable_jb_neg4.const_mul (A * B)).integrableOn (ha.mul hb) (fun x hx => ?_)
  show ‖a x * b x‖ ≤ A * B * B0579.jb x ^ (-4 : ℝ)
  rw [Real.norm_eq_abs, abs_mul]
  exact abs_mul_le_of_decay (B0579.jb_pos x) hA0 hB0 (ha' x hx) (hb' x hx)

/-- The `η`-compactly supported integrands are integrable on the cell. -/
theorem integrableOn_cut {c R : ℝ} {f : B0579.Plane → ℝ} (hf : Continuous f)
    (h0 : ∀ x : B0579.Plane, 2 * R < |x.2| → f x = 0) :
    IntegrableOn f (UnforcedLeray.Cyl.cell c) := by
  rw [← cell_eq c]
  exact DbCommon.integrableOn_cell_of_eta (R := 2 * R) hf h0

/-- `q`-flux `χ(η) (∂_q g · h - g · ∂_q h)`. -/
def q1 (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  DbCutoffAux.cutF R x.2 * (B0579.pd 0 g x * h x - g x * B0579.pd 0 h x)

/-- Its `q`-derivative `χ(η) (∂_q² g · h - g · ∂_q² h)`. -/
def q1' (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  DbCutoffAux.cutF R x.2 * (B0579.pd 0 (B0579.pd 0 g) x * h x - g x * B0579.pd 0 (B0579.pd 0 h) x)

/-- `η`-flux `χ(η) (∂_η g · h - g · ∂_η h)`. -/
def e2 (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  DbCutoffAux.cutF R x.2 * (B0579.pd 1 g x * h x - g x * B0579.pd 1 h x)

/-- The `χ'`-term of the `η`-derivative of `e2`. -/
def Yf (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  DbCutoffAux.cutD R x.2 * (B0579.pd 1 g x * h x - g x * B0579.pd 1 h x)

/-- The `χ`-term of the `η`-derivative of `e2`. -/
def Zf (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  DbCutoffAux.cutF R x.2 * (B0579.pd 1 (B0579.pd 1 g) x * h x - g x * B0579.pd 1 (B0579.pd 1 h) x)

/-- The `η`-derivative of `e2`. -/
def e2' (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  Yf R g h x + Zf R g h x

/-- The integrand `χ(η) (Δg · h - g · Δh)`. -/
def Xf (R : ℝ) (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  DbCutoffAux.cutF R x.2 * (lapP g x * h x - g x * lapP h x)

theorem hasDerivAt_q1 {R : ℝ} {g h : B0579.Plane → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (q η : ℝ) :
    HasDerivAt (fun t => q1 R g h (t, η)) (q1' R g h (q, η)) q := by
  have gd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have pgd : Differentiable ℝ (B0579.pd 0 g) :=
    (DbCommon.pd_contDiff_one hg 0).differentiable (by norm_num)
  have phd : Differentiable ℝ (B0579.pd 0 h) :=
    (DbCommon.pd_contDiff_one hh 0).differentiable (by norm_num)
  have s1 := DbCommon.hasDerivAt_slice_q gd q η
  have s2 := DbCommon.hasDerivAt_slice_q hd q η
  have s3 := DbCommon.hasDerivAt_slice_q pgd q η
  have s4 := DbCommon.hasDerivAt_slice_q phd q η
  have hJ := (s3.mul s2).sub (s1.mul s4)
  have hc := (hasDerivAt_const q (DbCutoffAux.cutF R η)).mul hJ
  have hfun : (fun t => q1 R g h (t, η)) = fun t => DbCutoffAux.cutF R η *
      (B0579.pd 0 g (t, η) * h (t, η) - g (t, η) * B0579.pd 0 h (t, η)) := rfl
  rw [hfun]
  refine hc.congr_deriv ?_
  unfold q1'
  dsimp only
  ring

theorem hasDerivAt_e2 {R : ℝ} {g h : B0579.Plane → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (q η : ℝ) :
    HasDerivAt (fun t => e2 R g h (q, t)) (e2' R g h (q, η)) η := by
  have gd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have pgd : Differentiable ℝ (B0579.pd 1 g) :=
    (DbCommon.pd_contDiff_one hg 1).differentiable (by norm_num)
  have phd : Differentiable ℝ (B0579.pd 1 h) :=
    (DbCommon.pd_contDiff_one hh 1).differentiable (by norm_num)
  have s1 := DbCommon.hasDerivAt_slice_eta gd q η
  have s2 := DbCommon.hasDerivAt_slice_eta hd q η
  have s3 := DbCommon.hasDerivAt_slice_eta pgd q η
  have s4 := DbCommon.hasDerivAt_slice_eta phd q η
  have hJ := (s3.mul s2).sub (s1.mul s4)
  have hc := (DbCutoffAux.hasDerivAt_cutF R η).mul hJ
  have hfun : (fun t => e2 R g h (q, t)) = fun t => DbCutoffAux.cutF R t *
      (B0579.pd 1 g (q, t) * h (q, t) - g (q, t) * B0579.pd 1 h (q, t)) := rfl
  rw [hfun]
  refine hc.congr_deriv ?_
  unfold e2' Yf Zf
  dsimp only
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

theorem cutF_zero_of {R : ℝ} (hR : 0 < R) {x : B0579.Plane} (hx : 2 * R < |x.2|) :
    DbCutoffAux.cutF R x.2 = 0 :=
  DbCutoffAux.cutF_eq_zero hR hx.le

/-- Convergence of the `η`-cut-off integrals `∫ χ_{n+1}(η) f` to `∫ f` (dominated convergence). -/
theorem tendsto_cutF {c : ℝ} {f : B0579.Plane → ℝ} (hf : Continuous f)
    (hfi : IntegrableOn f (UnforcedLeray.Cyl.cell c)) :
    Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c,
      DbCutoffAux.cutF ((n : ℝ) + 1) z.2 * f z) atTop (𝓝 (∫ z in UnforcedLeray.Cyl.cell c, f z)) := by
  have hcont : ∀ n : ℕ, Continuous fun z : B0579.Plane =>
      DbCutoffAux.cutF ((n : ℝ) + 1) z.2 * f z :=
    fun n => ((DbCutoffAux.cutF_contDiff _).continuous.comp continuous_snd).mul hf
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖)
    (Eventually.of_forall fun n => (hcont n).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun z => ?_) hfi.norm
    (ae_of_all _ fun z => ?_)
  · rw [norm_mul, Real.norm_of_nonneg (DbCutoffAux.cutF_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (DbCutoffAux.cutF_le_one _ _)
  · have hev : (fun n : ℕ => DbCutoffAux.cutF ((n : ℝ) + 1) z.2 * f z) =ᶠ[atTop]
        fun _ : ℕ => f z := by
      filter_upwards [eventually_ge_atTop ⌈|z.2|⌉₊] with n hn
      have h1 : |z.2| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have hc1 : DbCutoffAux.cutF ((n : ℝ) + 1) z.2 = 1 :=
        DbCutoffAux.cutF_eq_one (by positivity) (by linarith)
      rw [hc1, one_mul]
    exact tendsto_const_nhds.congr' hev.symm

end RtdLapAux

/-- **Leaf 3: integration by parts of the Laplacian on the cell** (SP 2097-2101). -/
theorem rtdLapIBP : UnforcedLeray.Short.IIb.RtdLapIBP := by
  intro c hc g h hg hh
  have hC2 : ContDiff ℝ 2 g := hg.smooth
  have hC2h : ContDiff ℝ 2 h := hh.smooth
  have hgc : Continuous g := hC2.continuous
  have hhc : Continuous h := hC2h.continuous
  rw [RtdLapAux.cell_eq c]
  obtain ⟨Cg, hCg0, hCg⟩ := RtdLapAux.strip_bounds hg
  obtain ⟨Ch, hCh0, hCh⟩ := RtdLapAux.strip_bounds hh
  -- integrability of the products on the cell
  have iLh : IntegrableOn (fun x => lapP g x * h x) (UnforcedLeray.Cyl.cell c) :=
    RtdLapAux.integrable_mul_strip (DbCommon.continuous_lapP hC2) hhc hCg0 hCh0
      (fun x hx => (hCg x hx).2.2.2) (fun x hx => (hCh x hx).1)
  have iGL : IntegrableOn (fun x => g x * lapP h x) (UnforcedLeray.Cyl.cell c) :=
    RtdLapAux.integrable_mul_strip hgc (DbCommon.continuous_lapP hC2h) hCg0 hCh0
      (fun x hx => (hCg x hx).1) (fun x hx => (hCh x hx).2.2.2)
  have iJ1 : IntegrableOn (fun x => B0579.pd 1 g x * h x) (UnforcedLeray.Cyl.cell c) :=
    RtdLapAux.integrable_mul_strip (DbCommon.continuous_pd_of_c2 hC2 1) hhc hCg0 hCh0
      (fun x hx => (hCg x hx).2.2.1) (fun x hx => (hCh x hx).1)
  have iJ2 : IntegrableOn (fun x => g x * B0579.pd 1 h x) (UnforcedLeray.Cyl.cell c) :=
    RtdLapAux.integrable_mul_strip hgc (DbCommon.continuous_pd_of_c2 hC2h 1) hCg0 hCh0
      (fun x hx => (hCg x hx).1) (fun x hx => (hCh x hx).2.2.1)
  have iJ : IntegrableOn (fun x => B0579.pd 1 g x * h x - g x * B0579.pd 1 h x)
      (UnforcedLeray.Cyl.cell c) := iJ1.sub iJ2
  have hffi : IntegrableOn (fun x => lapP g x * h x - g x * lapP h x)
      (UnforcedLeray.Cyl.cell c) := iLh.sub iGL
  have hffc : Continuous (fun x => lapP g x * h x - g x * lapP h x) :=
    ((DbCommon.continuous_lapP hC2).mul hhc).sub (hgc.mul (DbCommon.continuous_lapP hC2h))
  obtain ⟨K, hK0, hK⟩ := DbCutoffAux.exists_cutD_bound
  have hcutF : ∀ R : ℝ, Continuous fun x : B0579.Plane => DbCutoffAux.cutF R x.2 :=
    fun R => (DbCutoffAux.cutF_contDiff R).continuous.comp continuous_snd
  have hcutD : ∀ R : ℝ, Continuous fun x : B0579.Plane => DbCutoffAux.cutD R x.2 := by
    intro R
    have h1 : Continuous fun η : ℝ => DbCutoffAux.cutD R η := by
      unfold DbCutoffAux.cutD
      exact continuous_const.mul
        (DbCutoffAux.continuous_deriv_cutBump.comp (continuous_const.mul continuous_id))
    exact h1.comp continuous_snd
  have hiY : ∀ R : ℝ, 0 < R → IntegrableOn (RtdLapAux.Yf R g h) (UnforcedLeray.Cyl.cell c) := by
    intro R hR
    have hYc : Continuous (RtdLapAux.Yf R g h) :=
      (hcutD R).mul (((DbCommon.continuous_pd_of_c2 hC2 1).mul hhc).sub
        (hgc.mul (DbCommon.continuous_pd_of_c2 hC2h 1)))
    refine Integrable.mono' (iJ.norm.const_mul (K * (1 / R))) hYc.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    show ‖DbCutoffAux.cutD R x.2 * (B0579.pd 1 g x * h x - g x * B0579.pd 1 h x)‖ ≤
      K * (1 / R) * ‖B0579.pd 1 g x * h x - g x * B0579.pd 1 h x‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hK R x.2 hR) (abs_nonneg _)
  -- the per-radius identity `∫ χ_R (Δg h - g Δh) = -∫ χ_R' (∂_η g h - g ∂_η h)`
  have hid : ∀ R : ℝ, 0 < R → ∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.Xf R g h z
      = -∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.Yf R g h z := by
    intro R hR
    have iX : IntegrableOn (RtdLapAux.Xf R g h) (UnforcedLeray.Cyl.cell c) :=
      RtdLapAux.integrableOn_cut (R := R)
        ((hcutF R).mul (((DbCommon.continuous_lapP hC2).mul hhc).sub
          (hgc.mul (DbCommon.continuous_lapP hC2h))))
        (fun x hx => by unfold RtdLapAux.Xf; rw [RtdLapAux.cutF_zero_of hR hx, zero_mul])
    have iZ : IntegrableOn (RtdLapAux.Zf R g h) (UnforcedLeray.Cyl.cell c) :=
      RtdLapAux.integrableOn_cut (R := R)
        ((hcutF R).mul (((DbCommon.continuous_pd_pd hC2 1 1).mul hhc).sub
          (hgc.mul (DbCommon.continuous_pd_pd hC2h 1 1))))
        (fun x hx => by unfold RtdLapAux.Zf; rw [RtdLapAux.cutF_zero_of hR hx, zero_mul])
    have iE2 : IntegrableOn (RtdLapAux.e2 R g h) (UnforcedLeray.Cyl.cell c) :=
      RtdLapAux.integrableOn_cut (R := R)
        ((hcutF R).mul (((DbCommon.continuous_pd_of_c2 hC2 1).mul hhc).sub
          (hgc.mul (DbCommon.continuous_pd_of_c2 hC2h 1))))
        (fun x hx => by unfold RtdLapAux.e2; rw [RtdLapAux.cutF_zero_of hR hx, zero_mul])
    have iQ1 : IntegrableOn (RtdLapAux.q1' R g h) (UnforcedLeray.Cyl.cell c) :=
      RtdLapAux.integrableOn_cut (R := R)
        ((hcutF R).mul (((DbCommon.continuous_pd_pd hC2 0 0).mul hhc).sub
          (hgc.mul (DbCommon.continuous_pd_pd hC2h 0 0))))
        (fun x hx => by unfold RtdLapAux.q1'; rw [RtdLapAux.cutF_zero_of hR hx, zero_mul])
    have iE2' : IntegrableOn (RtdLapAux.e2' R g h) (UnforcedLeray.Cyl.cell c) :=
      Integrable.add (hiY R hR) iZ
    have hbd : ∀ η : ℝ, RtdLapAux.q1 R g h (c / 2, η) - RtdLapAux.q1 R g h (-c / 2, η) = 0 := by
      intro η
      have hgp : g (c / 2, η) = g (-c / 2, η) := by
        have h' : g (-c / 2 + c, η) = g (-c / 2, η) := hg.periodic (-c / 2, η)
        rw [show -c / 2 + c = c / 2 by ring] at h'
        exact h'
      have hhp : h (c / 2, η) = h (-c / 2, η) := by
        have h' : h (-c / 2 + c, η) = h (-c / 2, η) := hh.periodic (-c / 2, η)
        rw [show -c / 2 + c = c / 2 by ring] at h'
        exact h'
      have hpg : B0579.pd 0 g (c / 2, η) = B0579.pd 0 g (-c / 2, η) := by
        have h' := DbCommon.pd0_periodic hC2 hg.periodic (-c / 2) η
        rw [show -c / 2 + c = c / 2 by ring] at h'
        exact h'
      have hph : B0579.pd 0 h (c / 2, η) = B0579.pd 0 h (-c / 2, η) := by
        have h' := DbCommon.pd0_periodic hC2h hh.periodic (-c / 2) η
        rw [show -c / 2 + c = c / 2 by ring] at h'
        exact h'
      unfold RtdLapAux.q1
      dsimp only
      rw [hgp, hhp, hpg, hph]
      ring
    have hq1 : ∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.q1' R g h z = 0 := by
      rw [UnforcedLeray.Cyl.integral_cell_deriv_q (F := RtdLapAux.q1 R g h)
        (F' := RtdLapAux.q1' R g h) hc (fun q η => RtdLapAux.hasDerivAt_q1 hC2 hC2h q η) iQ1]
      simp only [hbd, integral_zero]
    have he2 : ∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.e2' R g h z = 0 :=
      UnforcedLeray.Cyl.integral_cell_deriv_eta (F := RtdLapAux.e2 R g h)
        (F' := RtdLapAux.e2' R g h) (fun q η => RtdLapAux.hasDerivAt_e2 hC2 hC2h q η) iE2 iE2'
    have hpw : ∀ z : B0579.Plane, RtdLapAux.q1' R g h z + RtdLapAux.e2' R g h z
        = RtdLapAux.Xf R g h z + RtdLapAux.Yf R g h z := by
      intro z
      unfold RtdLapAux.q1' RtdLapAux.e2' RtdLapAux.Yf RtdLapAux.Zf RtdLapAux.Xf
      unfold lapP
      ring
    have hsum0 : ∫ z in UnforcedLeray.Cyl.cell c, (RtdLapAux.Xf R g h z + RtdLapAux.Yf R g h z)
        = 0 := by
      calc ∫ z in UnforcedLeray.Cyl.cell c, (RtdLapAux.Xf R g h z + RtdLapAux.Yf R g h z)
          = ∫ z in UnforcedLeray.Cyl.cell c, (RtdLapAux.q1' R g h z + RtdLapAux.e2' R g h z) :=
            integral_congr_ae (ae_of_all _ fun z => (hpw z).symm)
        _ = (∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.q1' R g h z)
            + ∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.e2' R g h z := integral_add iQ1 iE2'
        _ = 0 := by rw [hq1, he2, add_zero]
    rw [integral_add iX (hiY R hR)] at hsum0
    linarith
  -- the bound `|∫ χ_R' J| ≤ K/R ∫ |J|`
  have hYbound : ∀ R : ℝ, 0 < R → ‖∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.Yf R g h z‖
      ≤ K * (1 / R) * ∫ z in UnforcedLeray.Cyl.cell c,
          ‖B0579.pd 1 g z * h z - g z * B0579.pd 1 h z‖ := by
    intro R hR
    calc ‖∫ z in UnforcedLeray.Cyl.cell c, RtdLapAux.Yf R g h z‖
        ≤ ∫ z in UnforcedLeray.Cyl.cell c, K * (1 / R) * ‖B0579.pd 1 g z * h z - g z * B0579.pd 1 h z‖ :=
          norm_integral_le_of_norm_le (iJ.norm.const_mul (K * (1 / R)))
            (ae_of_all _ fun z => by
              show ‖DbCutoffAux.cutD R z.2 * (B0579.pd 1 g z * h z - g z * B0579.pd 1 h z)‖ ≤ _
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
              exact mul_le_mul_of_nonneg_right (hK R z.2 hR) (abs_nonneg _))
      _ = K * (1 / R) * ∫ z in UnforcedLeray.Cyl.cell c,
          ‖B0579.pd 1 g z * h z - g z * B0579.pd 1 h z‖ := by
          rw [integral_const_mul]
  have hYlim : Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c,
      RtdLapAux.Yf ((n : ℝ) + 1) g h z) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => K * (1 / ((n : ℝ) + 1)) *
      ∫ z in UnforcedLeray.Cyl.cell c, ‖B0579.pd 1 g z * h z - g z * B0579.pd 1 h z‖)
      (fun n => hYbound _ (by positivity)) ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const
      (∫ z in UnforcedLeray.Cyl.cell c, ‖B0579.pd 1 g z * h z - g z * B0579.pd 1 h z‖)
    simpa using this
  have hXlim : Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c,
      RtdLapAux.Xf ((n : ℝ) + 1) g h z) atTop
      (𝓝 (∫ z in UnforcedLeray.Cyl.cell c, (lapP g z * h z - g z * lapP h z))) :=
    RtdLapAux.tendsto_cutF hffc hffi
  have hXlim0 : Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c,
      RtdLapAux.Xf ((n : ℝ) + 1) g h z) atTop (𝓝 0) := by
    have h1 := hYlim.neg
    rw [neg_zero] at h1
    refine h1.congr (fun n => ?_)
    exact (hid ((n : ℝ) + 1) (by positivity)).symm
  have hfz : ∫ z in UnforcedLeray.Cyl.cell c, (lapP g z * h z - g z * lapP h z) = 0 :=
    tendsto_nhds_unique hXlim hXlim0
  rw [integral_sub iLh iGL] at hfz
  refine ⟨iLh, iGL, ?_⟩
  linarith

end UnforcedLeray.Short.IIb
