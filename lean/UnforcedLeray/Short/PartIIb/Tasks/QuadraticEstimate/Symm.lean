import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.PairLin
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedFieldRepMinimalAE
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqRealSymm
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOSymm
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf1
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf3
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf4
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf6
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf7
import UnforcedLeray.Lib.AxisymmetricB.Average
import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!
# Realness and `𝒪`-symmetry of the quadratic convection field (`PartII-b:Q1` helper)

Source of record: `the November 2 reference manuscript`, lines 2503-2518, with
the class (2.2) of real `𝒪`-invariant fields.

* `mem_realSub_of_ae`: an element of `Y_{q₀}` represented by an a.e. real field is real;
  `grad_mem_realSub`: the weak gradient of a real field is real; `rep_im_zero_ae`.
* `mem_Osym_of_ae`: an element of `Y_{q₀}` represented by an a.e. `𝒪`-invariant field is in the
  class (2.2); `ae_gAct_of_pair`: a field in `Y_p` whose pairings are
  `⟪Φ, W⟫ = -⟪(u·∇)Φ, v⟫` with a.e. invariant `u, v` is a.e. invariant (chain rule `gAct_advT`,
  `gActPair`, `phaseFundamental`);
* `gAct_uOf_ae`: the state field `p.uOf z = e + w` is a.e. `𝒪`-invariant (axisymmetric inlet,
  `w ∈ X_{q₀}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.QuadLeaf

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412
  UnforcedLeray.B0411

/-! ## Realness -/

/-- `realC` as a real-linear continuous map. -/
def realCLq : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => realC x
      map_add' := fun x y => by ext i; simp [realC_apply]
      map_smul' := fun c x => by ext i; simp [realC_apply, Complex.real_smul] }

theorem dy_realC {φ : ℝ × Space → Space} (hφ : Differentiable ℝ φ) (j : Fin 3) :
    dy j (fun x => realC (φ x)) = fun x => realC (dy j φ x) := by
  funext x
  have h := (realCLq.hasFDerivAt.comp x (hφ x).hasFDerivAt).fderiv
  show fderiv ℝ (realCLq ∘ φ) x (0, coordinateVector j) =
    realCLq (fderiv ℝ φ x (0, coordinateVector j))
  rw [h]
  rfl

/-- The weak gradient of a real element of `Y_{q₀}` is real. -/
theorem grad_mem_realSub {P : ℝ} [Fact (0 < P)] {w : Yq P q0E} (hw : w ∈ realSub P q0E)
    {g : Fin 3 → Yq P q0E} (hg : UnforcedLeray.Short.PartIIa.HasGrad w g) (j : Fin 3) :
    g j ∈ realSub P q0E := by
  rw [mem_realSub] at hw ⊢
  intro φ hφ
  have h := hg j (fun x => realC (φ x)) (isPhaseTest_realC_yr φ hφ)
  have hφ' : IsPhaseTest P (fun x => -dy j φ x) := (hφ.dy j).neg
  have heq : (-dy j fun x => realC (φ x)) = fun x => realC (-dy j φ x) := by
    rw [dy_realC (hφ.smooth.differentiable (by simp)) j]
    funext x
    ext i
    simp [realC_apply]
  rw [← h]
  change (phasePair P q0E (-dy j fun x => realC (φ x)) w).im = 0
  rw [heq]
  exact hw _ hφ'

/-- A real element of `Y_{q₀}` has an a.e. real representative. -/
theorem rep_im_zero_ae {P : ℝ} [Fact (0 < P)] {w : Yq P q0E} (hw : w ∈ realSub P q0E) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ i : Fin 3, (rep w x.1 x.2 i).im = 0 := by
  have h := rep_real_ae_of_realSub w hw
  rw [← Measure.volume_eq_prod] at h
  filter_upwards [h] with x hx i
  have := congrArg (fun v : CVec3 => (v i).im) hx
  simpa [RieszLp.ofReV_apply] using this

/-- An element of `Y_{q₀}` represented by an a.e. real field is real. -/
theorem mem_realSub_of_ae {P : ℝ} [Fact (0 < P)] {F : Yq P q0E} {W : ℝ × Space → CVec3}
    (hW : HasRep F W)
    (hreal : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ i : Fin 3, (W x i).im = 0) :
    F ∈ realSub P q0E := by
  rw [mem_realSub]
  intro φ hφ
  let r : ℝ × Space → Space := fun x => WithLp.toLp 2 fun i => (W x i).re
  have hr : W =ᵐ[volume] fun x => realC (r x) := by
    filter_upwards [hreal] with x hx
    ext i
    rw [realC_apply]
    exact Complex.ext (by simp [r]) (by simp [r, hx i])
  rw [phasePair_eq_pairF_rep (isPhaseTest_realC_yr φ hφ) F, pairF_rep_eq P F W hW,
    pairF_congr_ae2 P (EventuallyEq.refl _ _) hr]
  exact pairF_realC_im_yr φ r

/-! ## `𝒪`-symmetry -/

/-- An element of `Y_{q₀}` represented by an a.e. `𝒪`-invariant field is in the class (2.2). -/
theorem mem_Osym_of_ae {P : ℝ} [Fact (0 < P)] {F : Yq P q0E} {W : ℝ × Space → CVec3}
    (hW : HasRep F W)
    (hWO : ∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g → W =ᵐ[volume] gAct g W) :
    F ∈ Osym P q0E := by
  rw [mem_Osym, isOInvariant_iff]
  intro g hg
  have hmp : MeasurePreserving g.symm volume volume :=
    LinearIsometryEquiv.measurePreserving g.symm
  refine ae_circle_of_ae_real_yo
    (p := fun θ => ∀ᵐ y ∂(volume : Measure Space), gC g (F θ (g.symm y)) = F θ y) ?_
  have hprod : ∀ᵐ x : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      W x = gAct g W x := by
    rw [← Measure.volume_eq_prod]
    exact hWO g hg
  filter_upwards [hW.slice, Measure.ae_ae_of_ae_prod hprod] with t ht hto
  have h1 : ∀ᵐ y ∂(volume : Measure Space), W (t, y) = F (t : AddCircle P) y := ht
  have h2 : ∀ᵐ y ∂(volume : Measure Space), W (t, g.symm y) = F (t : AddCircle P) (g.symm y) :=
    (hmp.quasiMeasurePreserving).ae
      (p := fun z => W (t, z) = F (t : AddCircle P) z) h1
  filter_upwards [h1, h2, hto] with y e1 e2 e3
  rw [← e2, ← e1]
  exact e3.symm

/-- Chain rule: `g·((v·∇)(g⁻¹·Φ)) = ((g·v)·∇)Φ`. -/
theorem gAct_advT (g : Space ≃ₗᵢ[ℝ] Space) (v : ℝ × Space → CVec3) {Φ : ℝ × Space → CVec3}
    (hΦ : Differentiable ℝ Φ) :
    gAct g (advT v (gAct g.symm Φ)) = advT (gAct g v) Φ := by
  funext x
  obtain ⟨t, y⟩ := x
  have hd : ∀ k : Fin 3, dy k (gAct g.symm Φ) (t, g.symm y) =
      gC g.symm (fderiv ℝ Φ (t, y) (0, g (coordinateVector k))) := by
    intro k
    show fderiv ℝ (gAct g.symm Φ) (t, g.symm y) (0, coordinateVector k) = _
    rw [GActLeaf3.fderiv_gAct_leaf3 g.symm Φ hΦ]
    simp
  have hdec : ∀ w : Space, fderiv ℝ Φ (t, y) (0, w) =
      ∑ j : Fin 3, ((w j : ℝ) : ℂ) • dy j Φ (t, y) := by
    intro w
    have hsum : ((0 : ℝ), w) = ∑ j : Fin 3, w j • ((0 : ℝ), coordinateVector j) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum]
        ext i
        simp [coordinateVector, Pi.single_apply]
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Complex.coe_smul]
    rfl
  have hgC : ∀ w : CVec3, gC g (gC g.symm w) = w := by
    intro w
    simpa using GActLeaf1.gC_symm_gC_leaf1 g.symm w
  simp only [gAct, advT]
  rw [map_sum]
  simp only [map_smul, hd, hgC, hdec, gC_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

/-- Pairing identity for the transformed field. -/
theorem pairF_gAct_eq_of_pair {P : ℝ} {W u v : ℝ × Space → CVec3}
    (hpair : ∀ Φ, IsPhaseTest P Φ → pairF P Φ W = -pairF P (advT u Φ) v)
    {g : Space ≃ₗᵢ[ℝ] Space} (hu : gAct g u =ᵐ[volume] u) (hv : gAct g v =ᵐ[volume] v)
    (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    pairF P Φ W = pairF P Φ (gAct g W) := by
  have hΦ' : IsPhaseTest P (gAct g.symm Φ) := _root_.gActPhaseTest P g.symm Φ hΦ
  have hinv : gAct g (gAct g.symm Φ) = Φ := by
    simpa using _root_.gActInv g.symm Φ
  have hmid : pairF P (advT u Φ) v = pairF P (advT u (gAct g.symm Φ)) v := by
    rw [← _root_.gActPair P g (advT u (gAct g.symm Φ)) v,
      gAct_advT g u (hΦ.smooth.differentiable (by simp))]
    exact pairF_congr_ae2 P (advT_congr_ae hu Φ).symm hv.symm
  calc pairF P Φ W = -pairF P (advT u Φ) v := hpair Φ hΦ
    _ = -pairF P (advT u (gAct g.symm Φ)) v := by rw [hmid]
    _ = pairF P (gAct g.symm Φ) W := (hpair _ hΦ').symm
    _ = pairF P (gAct g (gAct g.symm Φ)) (gAct g W) := (_root_.gActPair P g _ W).symm
    _ = pairF P Φ (gAct g W) := by rw [hinv]

/-- A field of `Y_p` with pairings `⟪Φ, W⟫ = -⟪(u·∇)Φ, v⟫` for a.e. invariant `u, v` is a.e.
invariant. -/
theorem ae_gAct_of_pair {P : ℝ} (hP : 0 < P) {W u v : ℝ × Space → CVec3}
    (hW : IsInYr P bgp W)
    (hpair : ∀ Φ, IsPhaseTest P Φ → pairF P Φ W = -pairF P (advT u Φ) v)
    {g : Space ≃ₗᵢ[ℝ] Space} (hu : gAct g u =ᵐ[volume] u) (hv : gAct g v =ᵐ[volume] v) :
    W =ᵐ[volume] gAct g W :=
  phaseFundamental P bgp W (gAct g W) hP (by norm_num [bgp]) hW (gActInYr P bgp g W hP hW)
    (fun Φ hΦ => pairF_gAct_eq_of_pair hpair hu hv Φ hΦ)

/-! ## The state field is real and `𝒪`-invariant -/

theorem nv_equivar {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (R τ : ℝ)
    (b : ℝ × (ℝ × ℝ) → Axi.Merid) (y : Space) :
    Axi.Nv R b τ (g y) = g (Axi.Nv R b τ y) := by
  have he3 : g Axi.e3 = Axi.e3 := hg
  have hage : Axi.age R (g y) = Axi.age R y := by
    simp only [Axi.age, Axi.ϱ_map hg]
  have hchart : Axi.chart R τ (g y) = Axi.chart R τ y := by
    simp only [Axi.chart, Axi.phase, Axi.trans, hage, Axi.ϱ_map hg, Axi.apply_two_map hg]
  have hframe : ∀ v : Axi.Merid, Axi.frameL (g y) v = g (Axi.frameL y v) := by
    intro v
    rw [Axi.frameL_apply, Axi.frameL_apply, Axi.eR_map hg y, map_add, map_smul, map_smul, he3]
  simp only [Axi.Nv, hage, hchart]
  rw [hframe, map_smul]

theorem inlet_equivar (p : Params) (i : Fin 2) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : UnforcedLeray.FixesAxis g) (τ : ℝ) (y : Space) :
    p.inlet i τ (g y) = g (p.inlet i τ y) :=
  nv_equivar hg p.R τ (p.inletProfile i) y

theorem gAct_eFun (p : Params) (α : Fin 2 → ℝ) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : UnforcedLeray.FixesAxis g) : gAct g (p.eFun α) = p.eFun α := by
  funext x
  obtain ⟨t, y⟩ := x
  simp only [gAct, Params.eFun, gC_realC, map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inlet_equivar p i hg, LinearIsometryEquiv.apply_symm_apply]

theorem wOf_mem (p : Params) (z : p.Z) :
    p.wOf z ∈ realSub p.period q0E ∧ p.wOf z ∈ Osym p.period q0E := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  obtain ⟨hX, hR⟩ := (mem_graphSpace p.period).1 z.2
  obtain ⟨hw, -, -⟩ := mem_XGraph_iff.1 hX
  exact ⟨hR, X_le_Osym hw⟩

/-- An element of the class (2.2) has an a.e. invariant joint representative. -/
theorem rep_gAct_ae {P : ℝ} [Fact (0 < P)] {w : Yq P q0E} (hw : w ∈ Osym P q0E)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), gC g (rep w x.1 (g.symm x.2)) = rep w x.1 x.2 := by
  have hO := (isOInvariant_iff w).1 ((mem_Osym).1 hw) g hg
  have hline := Axi.ae_Ioc_of_ae_circle (P := P) hO
  have hmp : MeasurePreserving g.symm volume volume :=
    LinearIsometryEquiv.measurePreserving g.symm
  let G : ℝ × Space → CVec3 := fun x => gC g (rep w x.1 (g.symm x.2)) - rep w x.1 x.2
  have hGm : Measurable G := by
    have h1 : StronglyMeasurable (fun x : ℝ × Space => rep w x.1 (g.symm x.2)) :=
      (stronglyMeasurable_rep w).comp_measurable
        (measurable_fst.prodMk (g.symm.continuous.measurable.comp measurable_snd))
    exact (((gC g).continuous.comp_stronglyMeasurable h1).sub
      (stronglyMeasurable_rep w)).measurable
  have hper : ∀ (k : ℤ) (x : ℝ × Space), G (x.1 + (k : ℝ) * P, x.2) = G x := by
    intro k x
    simp only [G, BLRepLinAux.rep_int_shift]
  have hloc : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ᵐ y ∂(volume : Measure Space),
      G (t, y) = 0 := by
    filter_upwards [hline] with t ht
    have h1 := rep_slice w t
    have h2 : ∀ᵐ y ∂(volume : Measure Space),
        rep w t (g.symm y) = (w (t : AddCircle P) : Space → CVec3) (g.symm y) :=
      (hmp.quasiMeasurePreserving).ae
        (p := fun z => rep w t z = (w (t : AddCircle P) : Space → CVec3) z) h1
    filter_upwards [ht, h1, h2] with y e e1 e2
    simp only [G, e1, e2, e, sub_self]
  have := BLRepLinAux.ae_zero_of_periodic (Fact.out : 0 < P) hGm hper hloc
  filter_upwards [this] with x hx
  exact sub_eq_zero.1 hx

/-- The state field `p.uOf z = e + w` is a.e. `𝒪`-invariant. -/
theorem gAct_uOf_ae (p : Params) (z : p.Z) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : UnforcedLeray.FixesAxis g) : gAct g (p.uOf z) =ᵐ[volume] p.uOf z := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  filter_upwards [rep_gAct_ae (wOf_mem p z).2 hg] with x hx
  have he := congrFun (gAct_eFun p (p.coord z) hg) x
  simp only [gAct] at he ⊢
  simp only [Params.uOf, map_add]
  rw [he, hx]

/-- The state field `p.uOf z = e + w` is a.e. real. -/
theorem uOf_im_zero_ae (p : Params) (z : p.Z) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ i : Fin 3, (p.uOf z x i).im = 0 := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  filter_upwards [rep_im_zero_ae (wOf_mem p z).1] with x hx i
  simp only [Params.uOf, Params.eFun, PiLp.add_apply, Complex.add_im, realC_apply,
    Complex.ofReal_im, zero_add, hx i]

end UnforcedLeray.Short.IIb.QuadLeaf
