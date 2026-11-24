import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.TrainJets
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.CylP0Smooth
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_7.Mixed

/-!
# Hilbert-Valued `H^∞(C_c)` Time-Derivative Tower on `(0, 2)`

Support module 3 for task `PartII-b:F8/1/org/2/3` (`RealCylOseenJointSmoothUpgrade`).
Constructs the tower `wSeq : ℕ → ℝ → B0579.Plane → F8Ex.RMerid` of successive time derivatives on
`(0, 2)` inside `C((0, 2); H^∞(C_c))` for spatially smooth Oseen slices `w` driven by the shifted
BUC train `V = F8Ex.shiftedDriftTrain tr σ`, and deduces the `BwdRoute.Joint.Tower` hypotheses on
every compact subinterval `[T₁, T₂] ⊂ (0, 2)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.F8JointUpgrade

open UnforcedLeray
open UnforcedLeray.Short.IIb

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Totalized `Cyl.L2v c` Curves, `IsHInfContOn`, and `HasHInfDerivOn` -/

/-- Totalized `Cyl.L2v c`-valued spatial derivative curve `s ↦ [∂^α (u s)]` (`0` outside `L²`). -/
def uL2 (c : ℝ) {n : ℕ} (α : Fin n → Fin 2) (u : ℝ → B0579.Plane → F8Ex.RMerid) (s : ℝ) :
    Cyl.L2v c :=
  open Classical in
  if h : MemLp (F8Ex.slicePdIterR α (u s)) 2 (F8Ex.cellMeas c) then
    toLpCell h
  else
    0

lemma uL2_eq_toLpCell {c : ℝ} {n : ℕ} (α : Fin n → Fin 2)
    {u : ℝ → B0579.Plane → F8Ex.RMerid} {s : ℝ}
    (hm : MemLp (F8Ex.slicePdIterR α (u s)) 2 (F8Ex.cellMeas c)) :
    uL2 c α u s = toLpCell hm :=
  dite_eq_left hm

lemma uL2_congr_slice {c : ℝ} {n : ℕ} (α : Fin n → Fin 2)
    {u v : ℝ → B0579.Plane → F8Ex.RMerid} {s : ℝ} (h : u s = v s) :
    uL2 c α u s = uL2 c α v s :=
  open Classical in
  congrArg
    (fun g => if hm : MemLp (F8Ex.slicePdIterR α g) 2 (F8Ex.cellMeas c) then toLpCell hm else 0) h

/-- `u` lies in `C((0, 2); H^∞(C_c))` with smooth `c`-periodic slices on `(0, 2)`. -/
structure IsHInfContOn (c : ℝ) (u : ℝ → B0579.Plane → F8Ex.RMerid) : Prop where
  hinf : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 → IsCylSmoothHInf c (u s)
  cont : ∀ {n : ℕ} (α : Fin n → Fin 2), ContinuousOn (uL2 c α u) (Ioo (0 : ℝ) 2)

/-- `u'` is the `H^∞(C_c)` time derivative of `u` on `(0, 2)`: every spatial derivative curve
`uL2 c α u` is Fréchet/time differentiable in `Cyl.L2v c` on `(0, 2)` with derivative `uL2 c α u'`. -/
structure HasHInfDerivOn (c : ℝ) (u u' : ℝ → B0579.Plane → F8Ex.RMerid) : Prop where
  u_cont : IsHInfContOn c u
  u'_cont : IsHInfContOn c u'
  hasDeriv : ∀ {n : ℕ} (α : Fin n → Fin 2) {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
    HasDerivAt (uL2 c α u) (uL2 c α u' s) s

lemma IsHInfContOn.continuousAt {c : ℝ} {u : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) {n : ℕ} (α : Fin n → Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    ContinuousAt (uL2 c α u) s :=
  (hu.cont α).continuousAt (isOpen_Ioo.mem_nhds hs)

lemma IsHInfContOn.uL2_eq {c : ℝ} {u : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) {n : ℕ} (α : Fin n → Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    uL2 c α u s = toLpCell ((hu.hinf hs).memL2 n α) :=
  uL2_eq_toLpCell α ((hu.hinf hs).memL2 n α)

/-! ## 2. Pointwise Joint Continuity (`SpSmooth`) and Pointwise Time Derivatives (`HasTimeDeriv`) -/

lemma pdW_comp_eq_slicePdIterR (l : List (Fin 2)) {g : B0579.Plane → F8Ex.RMerid}
    (hg : ContDiff ℝ ∞ g) (k : Fin 2) (y : B0579.Plane) :
    BwdRoute.pdW l (fun z => g z k) y = F8Ex.slicePdIterR l.get g y k := by
  induction l generalizing y with
  | nil => rfl
  | cons j l ih =>
      have ih_fn : BwdRoute.pdW l (fun z => g z k) =
          fun z => F8Ex.slicePdIterR l.get g z k :=
        funext ih
      have hsm_l : ContDiff ℝ ∞ (F8Ex.slicePdIterR l.get g) :=
        contDiff_slicePdIterR hg l.get
      have hdiff_l : DifferentiableAt ℝ (F8Ex.slicePdIterR l.get g) y :=
        (hsm_l.differentiable (by simp)) y
      have htail : Fin.tail (j :: l).get = l.get := by
        funext i
        rfl
      simp only [BwdRoute.pdW, ih_fn, B0579.pd]
      rw [PartI.csb_fderiv_comp_apply hdiff_l k (B0579.dir j)]
      simp only [F8Ex.slicePdIterR, htail]
      rfl

/-- Pointwise spatial-jet difference bound on `(0, 2)` from `norm_le_H2_of_isCylSmoothHInf`. -/
lemma norm_slicePdIterR_sub_le_uL2 {c : ℝ} (hc : 0 < c)
    {u : ℝ → B0579.Plane → F8Ex.RMerid} (hu : IsHInfContOn c u)
    {n : ℕ} (α : Fin n → Fin 2) {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (ht : t ∈ Ioo (0 : ℝ) 2)
    (y : B0579.Plane) :
    ‖F8Ex.slicePdIterR α (u t) y - F8Ex.slicePdIterR α (u s) y‖ ≤
      (2 * (32 * c⁻¹ + 64)) *
        ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2,
          ‖uL2 c (appendIdx β α) u t - uL2 c (appendIdx β α) u s‖ := by
  have hdiff : IsCylSmoothHInf c (F8Ex.slicePdIterR α (u t) - F8Ex.slicePdIterR α (u s)) :=
    ((hu.hinf ht).slicePdIterR α).sub ((hu.hinf hs).slicePdIterR α)
  have hb := norm_le_H2_of_isCylSmoothHInf hc hdiff y
  refine hb.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun β _ => ?_
  congr 1
  rw [hu.uL2_eq (appendIdx β α) ht, hu.uL2_eq (appendIdx β α) hs, ← toLpCell_sub]
  refine toLpCell_congr_ae _ _ (ae_of_all _ fun z => ?_)
  rw [slicePdIterR_sub (contDiff_slicePdIterR (hu.hinf ht).smooth α)
      (contDiff_slicePdIterR (hu.hinf hs).smooth α) β,
    slicePdIterR_slicePdIterR, slicePdIterR_slicePdIterR]

/-- Every spatial derivative of an `IsHInfContOn c` curve (`0 < c`) is jointly continuous on
`(0, 2) × ℝ²`. -/
lemma IsHInfContOn.continuousOn_slicePdIterR {c : ℝ} (hc : 0 < c)
    {u : ℝ → B0579.Plane → F8Ex.RMerid} (hu : IsHInfContOn c u)
    {n : ℕ} (α : Fin n → Fin 2) :
    ContinuousOn (fun x : Coord => F8Ex.slicePdIterR α (u x.1) x.2) (Ioo (0 : ℝ) 2 ×ˢ univ) := by
  rw [(isOpen_Ioo.prod isOpen_univ).continuousOn_iff]
  rintro ⟨s₀, y₀⟩ ⟨hs₀, -⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  set K : ℝ := 2 * (32 * c⁻¹ + 64)
  have hK_pos : 0 < K := by
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    dsimp [K]
    linarith
  have htend : Tendsto
      (fun s => K * ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2,
        ‖uL2 c (appendIdx β α) u s - uL2 c (appendIdx β α) u s₀‖) (𝓝 s₀) (𝓝 0) := by
    have hterm : ∀ (m : Fin 3) (β : Fin m.1 → Fin 2),
        Tendsto (fun s => ‖uL2 c (appendIdx β α) u s - uL2 c (appendIdx β α) u s₀‖)
          (𝓝 s₀) (𝓝 0) := fun m β =>
      tendsto_iff_norm_sub_tendsto_zero.mp (hu.continuousAt (appendIdx β α) hs₀)
    have hsum : Tendsto
        (fun s => ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2,
          ‖uL2 c (appendIdx β α) u s - uL2 c (appendIdx β α) u s₀‖) (𝓝 s₀) (𝓝 0) := by
      have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun m _ =>
        tendsto_finsetSum (Finset.univ : Finset (Fin m.1 → Fin 2)) fun β _ => hterm m β
      simpa using h1
    simpa using hsum.const_mul K
  have hev_s : ∀ᶠ s in 𝓝 s₀, s ∈ Ioo (0 : ℝ) 2 ∧
      K * (∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2,
        ‖uL2 c (appendIdx β α) u s - uL2 c (appendIdx β α) u s₀‖) < ε / 2 :=
    Filter.eventually_and.mpr ⟨isOpen_Ioo.mem_nhds hs₀,
      htend.eventually (gt_mem_nhds (half_pos hε))⟩
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hev_s
  have hcont_y : ContinuousAt (F8Ex.slicePdIterR α (u s₀)) y₀ :=
    (contDiff_slicePdIterR (hu.hinf hs₀).smooth α).continuous.continuousAt
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.continuousAt_iff.mp hcont_y (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ⟨s, y⟩ hxy => ?_⟩
  rw [Prod.dist_eq] at hxy
  have hs_dist : dist s s₀ < δ₁ :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hxy (min_le_left _ _))
  have hy_dist : dist y y₀ < δ₂ :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hxy (min_le_right _ _))
  obtain ⟨hs_mem, hs_lt⟩ := hball₁ hs_dist
  have hy_lt : dist (F8Ex.slicePdIterR α (u s₀) y) (F8Ex.slicePdIterR α (u s₀) y₀) < ε / 2 :=
    hball₂ hy_dist
  calc dist (F8Ex.slicePdIterR α (u s) y) (F8Ex.slicePdIterR α (u s₀) y₀)
      ≤ dist (F8Ex.slicePdIterR α (u s) y) (F8Ex.slicePdIterR α (u s₀) y) +
          dist (F8Ex.slicePdIterR α (u s₀) y) (F8Ex.slicePdIterR α (u s₀) y₀) :=
        dist_triangle _ _ _
    _ = ‖F8Ex.slicePdIterR α (u s) y - F8Ex.slicePdIterR α (u s₀) y‖ +
          dist (F8Ex.slicePdIterR α (u s₀) y) (F8Ex.slicePdIterR α (u s₀) y₀) := by
        rw [dist_eq_norm]
    _ ≤ K * (∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2,
          ‖uL2 c (appendIdx β α) u s - uL2 c (appendIdx β α) u s₀‖) +
          dist (F8Ex.slicePdIterR α (u s₀) y) (F8Ex.slicePdIterR α (u s₀) y₀) :=
        add_le_add (norm_slicePdIterR_sub_le_uL2 hc hu α hs₀ hs_mem y) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hs_lt hy_lt
    _ = ε := add_halves ε

/-- Restriction of an `IsHInfContOn c` curve (`0 < c`) to `[T₁, T₂] ⊂ (0, 2)` (shifted to
`[0, T₂ - T₁]`) belongs to `BwdRoute.SpSmooth (T₂ - T₁)` in each meridional component. -/
lemma IsHInfContOn.spSmooth {c : ℝ} (hc : 0 < c)
    {u : ℝ → B0579.Plane → F8Ex.RMerid} (hu : IsHInfContOn c u)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (_hT₁₂ : T₁ < T₂) (hT₂ : T₂ < 2) (k : Fin 2) :
    BwdRoute.SpSmooth (T₂ - T₁) (fun r y => u (T₁ + r) y k) where
  slice r hr := by
    have hr' : T₁ + r ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp (hu.hinf hr').smooth
  cont l := by
    have hmap : MapsTo (fun z : ℝ × B0579.Plane => ((T₁ + z.1, z.2) : Coord))
        (Icc 0 (T₂ - T₁) ×ˢ univ) (Ioo (0 : ℝ) 2 ×ˢ univ) := by
      rintro ⟨r, y⟩ ⟨hr, -⟩
      exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, trivial⟩
    have hsh_cont : Continuous (fun z : ℝ × B0579.Plane => ((T₁ + z.1, z.2) : Coord)) :=
      (continuous_const.add continuous_fst).prodMk continuous_snd
    have hvec : ContinuousOn (fun z : ℝ × B0579.Plane => F8Ex.slicePdIterR l.get (u (T₁ + z.1)) z.2)
        (Icc 0 (T₂ - T₁) ×ˢ univ) :=
      (hu.continuousOn_slicePdIterR hc l.get).comp hsh_cont.continuousOn hmap
    have hcomp : ContinuousOn
        (fun z : ℝ × B0579.Plane => F8Ex.slicePdIterR l.get (u (T₁ + z.1)) z.2 k)
        (Icc 0 (T₂ - T₁) ×ˢ univ) :=
      (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).continuous.comp_continuousOn hvec
    refine hcomp.congr ?_
    rintro ⟨r, y⟩ ⟨hr, -⟩
    have hr' : T₁ + r ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact pdW_comp_eq_slicePdIterR l (hu.hinf hr').smooth k y

/-- Every spatial derivative of `u` is pointwise time-differentiable on `(0, 2)` with derivative
equal to the corresponding spatial derivative of `u'`. -/
lemma HasHInfDerivOn.hasDerivAt_slicePdIterR {c : ℝ} (hc : 0 < c)
    {u u' : ℝ → B0579.Plane → F8Ex.RMerid} (hd : HasHInfDerivOn c u u')
    {n : ℕ} (α : Fin n → Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (y : B0579.Plane) :
    HasDerivAt (fun t => F8Ex.slicePdIterR α (u t) y) (F8Ex.slicePdIterR α (u' s) y) s := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  set K : ℝ := 2 * (32 * c⁻¹ + 64)
  have hK_pos : 0 < K := by
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    dsimp [K]
    linarith
  set η : ℝ := ε / (8 * K)
  have hη : 0 < η := div_pos hε (by positivity)
  have hev_one : ∀ (m : Fin 3) (β : Fin m.1 → Fin 2),
      ∀ᶠ h : ℝ in 𝓝 0,
        ‖uL2 c (appendIdx β α) u (s + h) - uL2 c (appendIdx β α) u s -
            h • uL2 c (appendIdx β α) u' s‖ ≤ η * ‖h‖ := by
    intro m β
    have hd_β := hd.hasDeriv (appendIdx β α) hs
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hd_β
    exact hd_β hη
  have hev_all : ∀ᶠ h : ℝ in 𝓝 0, ∀ (m : Fin 3) (β : Fin m.1 → Fin 2),
      ‖uL2 c (appendIdx β α) u (s + h) - uL2 c (appendIdx β α) u s -
          h • uL2 c (appendIdx β α) u' s‖ ≤ η * ‖h‖ :=
    eventually_all.mpr fun m => eventually_all.mpr fun β => hev_one m β
  have hev_mem : ∀ᶠ h : ℝ in 𝓝 0, s + h ∈ Ioo (0 : ℝ) 2 := by
    have hcont : ContinuousAt (fun h : ℝ => s + h) 0 := continuousAt_const.add continuousAt_id
    have h0 : s + (0 : ℝ) ∈ Ioo (0 : ℝ) 2 := by simpa using hs
    exact hcont.eventually (isOpen_Ioo.mem_nhds h0)
  filter_upwards [hev_mem, hev_all] with h hsh hall
  let rem : B0579.Plane → F8Ex.RMerid :=
    F8Ex.slicePdIterR α (u (s + h)) - F8Ex.slicePdIterR α (u s) -
      h • F8Ex.slicePdIterR α (u' s)
  have hrem_hinf : IsCylSmoothHInf c rem :=
    (((hd.u_cont.hinf hsh).slicePdIterR α).sub ((hd.u_cont.hinf hs).slicePdIterR α)).sub
      (((hd.u'_cont.hinf hs).slicePdIterR α).smul h)
  have hb := norm_le_H2_of_isCylSmoothHInf hc hrem_hinf y
  have hlp_eq : ∀ (m : Fin 3) (β : Fin m.1 → Fin 2),
      toLpCell (hrem_hinf.memL2 m.1 β) =
        uL2 c (appendIdx β α) u (s + h) - uL2 c (appendIdx β α) u s -
          h • uL2 c (appendIdx β α) u' s := by
    intro m β
    rw [hd.u_cont.uL2_eq (appendIdx β α) hsh, hd.u_cont.uL2_eq (appendIdx β α) hs,
      hd.u'_cont.uL2_eq (appendIdx β α) hs, ← toLpCell_smul, ← toLpCell_sub, ← toLpCell_sub]
    refine toLpCell_congr_ae _ _ (ae_of_all _ fun z => ?_)
    have hsm1 := contDiff_slicePdIterR (hd.u_cont.hinf hsh).smooth α
    have hsm2 := contDiff_slicePdIterR (hd.u_cont.hinf hs).smooth α
    have hsm12 : ContDiff ℝ ∞ (F8Ex.slicePdIterR α (u (s + h)) - F8Ex.slicePdIterR α (u s)) :=
      hsm1.sub hsm2
    have hsm3 := contDiff_slicePdIterR (hd.u'_cont.hinf hs).smooth α
    have hsm3h : ContDiff ℝ ∞ (h • F8Ex.slicePdIterR α (u' s)) := contDiff_const.smul hsm3
    dsimp [rem]
    rw [slicePdIterR_sub hsm12 hsm3h β,
      slicePdIterR_sub hsm1 hsm2 β, slicePdIterR_smul h hsm3 β,
      slicePdIterR_slicePdIterR, slicePdIterR_slicePdIterR, slicePdIterR_slicePdIterR]
    rfl
  have hsum_le : (∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2, ‖toLpCell (hrem_hinf.memL2 m.1 β)‖) ≤
      7 * (η * ‖h‖) := by
    have hcard_sum : (∑ m : Fin 3, ∑ _β : Fin m.1 → Fin 2, (1 : ℝ)) = 7 := by
      rw [Fin.sum_univ_three]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Finset.sum_const, Finset.card_univ,
        Fintype.card_pi, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul]
      norm_num
    calc ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2, ‖toLpCell (hrem_hinf.memL2 m.1 β)‖
        ≤ ∑ m : Fin 3, ∑ _β : Fin m.1 → Fin 2, (η * ‖h‖) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun β _ => ?_
          rw [hlp_eq m β]
          exact hall m β
      _ = (∑ m : Fin 3, ∑ _β : Fin m.1 → Fin 2, (1 : ℝ)) * (η * ‖h‖) := by
          simp [Finset.sum_mul]
      _ = 7 * (η * ‖h‖) := by rw [hcard_sum]
  calc ‖F8Ex.slicePdIterR α (u (s + h)) y - F8Ex.slicePdIterR α (u s) y -
          h • F8Ex.slicePdIterR α (u' s) y‖
      = ‖rem y‖ := rfl
    _ ≤ K * ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2, ‖toLpCell (hrem_hinf.memL2 m.1 β)‖ := hb
    _ ≤ K * (7 * (η * ‖h‖)) := mul_le_mul_of_nonneg_left hsum_le hK_pos.le
    _ ≤ K * (8 * (η * ‖h‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hη.le (norm_nonneg _)))
          hK_pos.le
    _ = ε * ‖h‖ := by
        dsimp [η]
        field_simp [hK_pos.ne']

lemma HasHInfDerivOn.hasTimeDeriv {c : ℝ} (hc : 0 < c)
    {u u' : ℝ → B0579.Plane → F8Ex.RMerid} (hd : HasHInfDerivOn c u u')
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (_hT₁₂ : T₁ < T₂) (hT₂ : T₂ < 2) (k : Fin 2) :
    BwdRoute.Joint.HasTimeDeriv (T₂ - T₁)
      (fun r y => u (T₁ + r) y k) (fun r y => u' (T₁ + r) y k) := by
  intro r hr y
  have hr' : T₁ + r ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hd_vec : HasDerivAt (fun t => u t y) (u' (T₁ + r) y) (T₁ + r) :=
    hd.hasDerivAt_slicePdIterR hc Fin.elim0 hr' y
  have hsh : HasDerivAt (fun t : ℝ => T₁ + t) 1 r := by
    simpa using (hasDerivAt_id' r).const_add T₁
  have hvec_sh : HasDerivAt (fun t => u (T₁ + t) y) ((1 : ℝ) • u' (T₁ + r) y) r :=
    hd_vec.scomp r hsh
  rw [one_smul] at hvec_sh
  have hcomp : HasDerivAt (fun t => u (T₁ + t) y k) (u' (T₁ + r) y k) r :=
    (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r hvec_sh
  exact hcomp.hasDerivWithinAt

/-! ## 3. Closure of `IsHInfContOn` and `HasHInfDerivOn` Under PDE Operators -/

namespace IsHInfContOn

lemma zero (c : ℝ) : IsHInfContOn c (fun _ => 0) where
  hinf _ := IsCylSmoothHInf.zero c
  cont α := by
    have heq : EqOn (uL2 c α (fun _ => 0)) (fun _ => 0) (Ioo (0 : ℝ) 2) := by
      intro s hs
      rw [uL2_eq_toLpCell α ((IsCylSmoothHInf.zero c).memL2 _ α)]
      refine (toLpCell_congr_ae _ MemLp.zero (ae_of_all _ fun y => ?_)).trans (toLpCell_zero c)
      rw [slicePdIterR_zero]
    exact continuousOn_const.congr heq

lemma add {c : ℝ} {u v : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) (hv : IsHInfContOn c v) :
    IsHInfContOn c (fun s => u s + v s) where
  hinf hs := (hu.hinf hs).add (hv.hinf hs)
  cont {n} α := by
    refine ((hu.cont α).add (hv.cont α)).congr fun s hs => ?_
    dsimp only [Pi.add_apply]
    rw [uL2_eq_toLpCell α (((hu.hinf hs).add (hv.hinf hs)).memL2 n α),
      hu.uL2_eq α hs, hv.uL2_eq α hs, ← toLpCell_add]
    exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
      rw [slicePdIterR_add (hu.hinf hs).smooth (hv.hinf hs).smooth α])

lemma smul {c : ℝ} (r : ℝ) {u : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) :
    IsHInfContOn c (fun s => r • u s) where
  hinf hs := (hu.hinf hs).smul r
  cont {n} α := by
    refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => r) (Ioo 0 2)).smul
      (hu.cont α)).congr fun s hs => ?_
    change uL2 c α (fun t => r • u t) s = r • uL2 c α u s
    rw [uL2_eq_toLpCell α (((hu.hinf hs).smul r).memL2 n α), hu.uL2_eq α hs, ← toLpCell_smul]
    exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
      rw [slicePdIterR_smul r (hu.hinf hs).smooth α])

lemma sub {c : ℝ} {u v : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) (hv : IsHInfContOn c v) :
    IsHInfContOn c (fun s => u s - v s) := by
  have h : (fun s => u s - v s) = fun s => u s + (-1 : ℝ) • v s := by
    funext s y
    simp [sub_eq_add_neg]
  rw [h]
  exact hu.add (hv.smul (-1))

lemma slicePdR {c : ℝ} {u : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) (d : Fin 2) :
    IsHInfContOn c (fun s => F8Ex.slicePdR d (u s)) where
  hinf hs := (hu.hinf hs).slicePdR d
  cont {n} α := by
    refine (hu.cont (snocIdx α d)).congr fun s hs => ?_
    rw [uL2_eq_toLpCell α (((hu.hinf hs).slicePdR d).memL2 n α),
      hu.uL2_eq (snocIdx α d) hs]
    exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by rw [slicePdIterR_slicePdR])

lemma P0Smooth {c : ℝ} (hc : 0 < c) {u : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) :
    IsHInfContOn c (fun s => F8JointUpgrade.P0Smooth c (u s)) where
  hinf hs := P0Smooth_isCylSmoothHInf hc (hu.hinf hs)
  cont {n} α := by
    refine ((Cyl.P0 c).continuous.comp_continuousOn (hu.cont α)).congr fun s hs => ?_
    dsimp only [Function.comp_apply]
    rw [uL2_eq_toLpCell α ((P0Smooth_isCylSmoothHInf hc (hu.hinf hs)).memL2 n α),
      hu.uL2_eq α hs]
    exact toLpCell_slicePdIterR_P0Smooth hc (hu.hinf hs) α

end IsHInfContOn

namespace HasHInfDerivOn

lemma zero (c : ℝ) : HasHInfDerivOn c (fun _ => 0) (fun _ => 0) where
  u_cont := IsHInfContOn.zero c
  u'_cont := IsHInfContOn.zero c
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α (fun _ => 0) =ᶠ[𝓝 s] fun _ => (0 : Cyl.L2v c) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t _
      rw [uL2_eq_toLpCell α ((IsCylSmoothHInf.zero c).memL2 n α)]
      refine (toLpCell_congr_ae _ MemLp.zero (ae_of_all _ fun y => ?_)).trans (toLpCell_zero c)
      rw [slicePdIterR_zero]
    have h0 : uL2 c α (fun _ => 0) s = 0 := hev.self_of_nhds
    rw [h0]
    exact (hasDerivAt_const s (0 : Cyl.L2v c)).congr_of_eventuallyEq hev

lemma add {c : ℝ} {u u' v v' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u') (hv : HasHInfDerivOn c v v') :
    HasHInfDerivOn c (fun s => u s + v s) (fun s => u' s + v' s) where
  u_cont := hu.u_cont.add hv.u_cont
  u'_cont := hu.u'_cont.add hv.u'_cont
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α (fun t => u t + v t) =ᶠ[𝓝 s] fun t => uL2 c α u t + uL2 c α v t := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      rw [uL2_eq_toLpCell α (((hu.u_cont.hinf ht).add (hv.u_cont.hinf ht)).memL2 n α),
        hu.u_cont.uL2_eq α ht, hv.u_cont.uL2_eq α ht, ← toLpCell_add]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
        rw [slicePdIterR_add (hu.u_cont.hinf ht).smooth (hv.u_cont.hinf ht).smooth α])
    have hd_eq : uL2 c α (fun t => u' t + v' t) s = uL2 c α u' s + uL2 c α v' s := by
      rw [uL2_eq_toLpCell α (((hu.u'_cont.hinf hs).add (hv.u'_cont.hinf hs)).memL2 n α),
        hu.u'_cont.uL2_eq α hs, hv.u'_cont.uL2_eq α hs, ← toLpCell_add]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
        rw [slicePdIterR_add (hu.u'_cont.hinf hs).smooth (hv.u'_cont.hinf hs).smooth α])
    rw [hd_eq]
    exact ((hu.hasDeriv α hs).add (hv.hasDeriv α hs)).congr_of_eventuallyEq hev

lemma smul {c : ℝ} (r : ℝ) {u u' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u') :
    HasHInfDerivOn c (fun s => r • u s) (fun s => r • u' s) where
  u_cont := hu.u_cont.smul r
  u'_cont := hu.u'_cont.smul r
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α (fun t => r • u t) =ᶠ[𝓝 s] fun t => r • uL2 c α u t := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      rw [uL2_eq_toLpCell α (((hu.u_cont.hinf ht).smul r).memL2 n α),
        hu.u_cont.uL2_eq α ht, ← toLpCell_smul]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
        rw [slicePdIterR_smul r (hu.u_cont.hinf ht).smooth α])
    have hd_eq : uL2 c α (fun t => r • u' t) s = r • uL2 c α u' s := by
      rw [uL2_eq_toLpCell α (((hu.u'_cont.hinf hs).smul r).memL2 n α),
        hu.u'_cont.uL2_eq α hs, ← toLpCell_smul]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
        rw [slicePdIterR_smul r (hu.u'_cont.hinf hs).smooth α])
    rw [hd_eq]
    exact ((hu.hasDeriv α hs).const_smul r).congr_of_eventuallyEq hev

lemma sub {c : ℝ} {u u' v v' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u') (hv : HasHInfDerivOn c v v') :
    HasHInfDerivOn c (fun s => u s - v s) (fun s => u' s - v' s) := by
  have h1 : (fun s => u s - v s) = fun s => u s + (-1 : ℝ) • v s := by
    funext s y
    simp [sub_eq_add_neg]
  have h2 : (fun s => u' s - v' s) = fun s => u' s + (-1 : ℝ) • v' s := by
    funext s y
    simp [sub_eq_add_neg]
  rw [h1, h2]
  exact hu.add (hv.smul (-1))

lemma slicePdR {c : ℝ} {u u' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u') (d : Fin 2) :
    HasHInfDerivOn c (fun s => F8Ex.slicePdR d (u s)) (fun s => F8Ex.slicePdR d (u' s)) where
  u_cont := hu.u_cont.slicePdR d
  u'_cont := hu.u'_cont.slicePdR d
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α (fun t => F8Ex.slicePdR d (u t)) =ᶠ[𝓝 s] uL2 c (snocIdx α d) u := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      rw [uL2_eq_toLpCell α (((hu.u_cont.hinf ht).slicePdR d).memL2 n α),
        hu.u_cont.uL2_eq (snocIdx α d) ht]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by rw [slicePdIterR_slicePdR])
    have hd_eq : uL2 c α (fun t => F8Ex.slicePdR d (u' t)) s = uL2 c (snocIdx α d) u' s := by
      rw [uL2_eq_toLpCell α (((hu.u'_cont.hinf hs).slicePdR d).memL2 n α),
        hu.u'_cont.uL2_eq (snocIdx α d) hs]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by rw [slicePdIterR_slicePdR])
    rw [hd_eq]
    exact (hu.hasDeriv (snocIdx α d) hs).congr_of_eventuallyEq hev

lemma P0Smooth {c : ℝ} (hc : 0 < c) {u u' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u') :
    HasHInfDerivOn c
      (fun s => F8JointUpgrade.P0Smooth c (u s))
      (fun s => F8JointUpgrade.P0Smooth c (u' s)) where
  u_cont := hu.u_cont.P0Smooth hc
  u'_cont := hu.u'_cont.P0Smooth hc
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α (fun t => F8JointUpgrade.P0Smooth c (u t)) =ᶠ[𝓝 s]
        fun t => Cyl.P0 c (uL2 c α u t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      rw [uL2_eq_toLpCell α ((P0Smooth_isCylSmoothHInf hc (hu.u_cont.hinf ht)).memL2 n α),
        hu.u_cont.uL2_eq α ht]
      exact toLpCell_slicePdIterR_P0Smooth hc (hu.u_cont.hinf ht) α
    have hd_eq : uL2 c α (fun t => F8JointUpgrade.P0Smooth c (u' t)) s =
        Cyl.P0 c (uL2 c α u' s) := by
      rw [uL2_eq_toLpCell α ((P0Smooth_isCylSmoothHInf hc (hu.u'_cont.hinf hs)).memL2 n α),
        hu.u'_cont.uL2_eq α hs]
      exact toLpCell_slicePdIterR_P0Smooth hc (hu.u'_cont.hinf hs) α
    rw [hd_eq]
    exact ((Cyl.P0 c).hasFDerivAt.comp_hasDerivAt s (hu.hasDeriv α hs)).congr_of_eventuallyEq hev

end HasHInfDerivOn

/-- Slice spatial Laplacian `(∂_q² + ∂_η²) f`. -/
def sliceLapR (f : B0579.Plane → F8Ex.RMerid) : B0579.Plane → F8Ex.RMerid :=
  F8Ex.slicePdR 0 (F8Ex.slicePdR 0 f) + F8Ex.slicePdR 1 (F8Ex.slicePdR 1 f)

lemma IsCylSmoothHInf.sliceLapR {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) : IsCylSmoothHInf c (F8JointUpgrade.sliceLapR f) :=
  ((hf.slicePdR 0).slicePdR 0).add ((hf.slicePdR 1).slicePdR 1)

lemma IsHInfContOn.sliceLapR {c : ℝ} {u : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) : IsHInfContOn c (fun s => F8JointUpgrade.sliceLapR (u s)) :=
  ((hu.slicePdR 0).slicePdR 0).add ((hu.slicePdR 1).slicePdR 1)

lemma HasHInfDerivOn.sliceLapR {c : ℝ} {u u' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u') :
    HasHInfDerivOn c
      (fun s => F8JointUpgrade.sliceLapR (u s))
      (fun s => F8JointUpgrade.sliceLapR (u' s)) :=
  ((hu.slicePdR 0).slicePdR 0).add ((hu.slicePdR 1).slicePdR 1)

/-- Constant linear map on `ℝ²` sending `v` to `(v k) • e_i`. -/
def eVec : Fin 2 → F8Ex.RMerid
  | 0 => Cyl.vec 1 0
  | 1 => Cyl.vec 0 1

@[simp] private lemma eVec_zero_zero : eVec 0 0 = 1 := by simp [eVec]
@[simp] private lemma eVec_zero_one : eVec 0 1 = 0 := by simp [eVec]
@[simp] private lemma eVec_one_zero : eVec 1 0 = 0 := by simp [eVec]
@[simp] private lemma eVec_one_one : eVec 1 1 = 1 := by simp [eVec]

def coordMap (k i : Fin 2) : F8Ex.RMerid →L[ℝ] F8Ex.RMerid :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (eVec i)).comp (EuclideanSpace.proj k)

@[simp]
private lemma coordMap_apply (k i l : Fin 2) (v : F8Ex.RMerid) :
    coordMap k i v l = v k * eVec i l := rfl

private lemma inner_smul_eVec (i : Fin 2) (a : ℝ) (v : F8Ex.RMerid) :
    ⟪a • eVec i, v⟫_ℝ = a * v i := by
  rw [real_inner_smul_left, real_inner_comm]
  revert i
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [eVec, Cyl.inner_vec]

lemma slicePdIterR_clm_comp (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) {f : B0579.Plane → F8Ex.RMerid},
      ContDiff ℝ ∞ f → F8Ex.slicePdIterR α (fun y => L (f y)) =
        fun y => L (F8Ex.slicePdIterR α f y)
  | 0, _, _, _ => rfl
  | _ + 1, α, f, hf => by
      simp only [F8Ex.slicePdIterR]
      rw [slicePdIterR_clm_comp L (Fin.tail α) hf]
      funext y
      have hd : DifferentiableAt ℝ (F8Ex.slicePdIterR (Fin.tail α) f) y :=
        ((contDiff_slicePdIterR hf (Fin.tail α)).differentiable (by simp)) y
      have hc := L.hasFDerivAt.comp y hd.hasFDerivAt
      change fderiv ℝ (L ∘ F8Ex.slicePdIterR (Fin.tail α) f) y (B0579.dir (α 0)) = _
      rw [hc.fderiv]
      rfl

private def clmL2v (c : ℝ) (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid) :
    Cyl.L2v c →L[ℝ] Cyl.L2v c :=
  L.compLpL 2 (Cyl.cellμ c)

private lemma clmL2v_toLpCell {c : ℝ} (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid)
    {f : B0579.Plane → F8Ex.RMerid} (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    clmL2v c L (toLpCell hf) = toLpCell (L.comp_memLp' hf) := by
  apply Lp.ext
  have h1 := L.coeFn_compLpL (p := 2) (μ := Cyl.cellμ c) (toLpCell hf)
  filter_upwards [h1, coeFn_toLpCell hf, coeFn_toLpCell (L.comp_memLp' hf)] with z hz1 hz2 hz3
  dsimp only [clmL2v, Function.comp_apply] at hz1 hz3 ⊢
  rw [hz1, hz2, hz3]

lemma IsHInfContOn.clm_comp {c : ℝ} (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid)
    {u : ℝ → B0579.Plane → F8Ex.RMerid} (hu : IsHInfContOn c u) :
    IsHInfContOn c (fun s y => L (u s y)) where
  hinf {s} hs :=
    { smooth := L.contDiff.comp (hu.hinf hs).smooth
      periodic := fun z => by simp [(hu.hinf hs).periodic z]
      memL2 := fun n α => by
        rw [slicePdIterR_clm_comp L α (hu.hinf hs).smooth]
        exact L.comp_memLp' ((hu.hinf hs).memL2 n α) }
  cont {n} α := by
    refine ((clmL2v c L).continuous.comp_continuousOn (hu.cont α)).congr fun s hs => ?_
    dsimp only [Function.comp_apply]
    have hm : MemLp (F8Ex.slicePdIterR α (fun y => L (u s y))) 2 (F8Ex.cellMeas c) := by
      rw [slicePdIterR_clm_comp L α (hu.hinf hs).smooth]
      exact L.comp_memLp' ((hu.hinf hs).memL2 n α)
    rw [uL2_eq_toLpCell α hm, hu.uL2_eq α hs, clmL2v_toLpCell]
    exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
      rw [slicePdIterR_clm_comp L α (hu.hinf hs).smooth]; rfl)

lemma HasHInfDerivOn.clm_comp {c : ℝ} (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid)
    {u u' : ℝ → B0579.Plane → F8Ex.RMerid} (hu : HasHInfDerivOn c u u') :
    HasHInfDerivOn c (fun s y => L (u s y)) (fun s y => L (u' s y)) where
  u_cont := hu.u_cont.clm_comp L
  u'_cont := hu.u'_cont.clm_comp L
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α (fun t y => L (u t y)) =ᶠ[𝓝 s] fun t => clmL2v c L (uL2 c α u t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      rw [(hu.u_cont.clm_comp L).uL2_eq α ht, hu.u_cont.uL2_eq α ht, clmL2v_toLpCell]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
        rw [slicePdIterR_clm_comp L α (hu.u_cont.hinf ht).smooth]; rfl)
    have hd_eq : uL2 c α (fun t y => L (u' t y)) s = clmL2v c L (uL2 c α u' s) := by
      rw [(hu.u'_cont.clm_comp L).uL2_eq α hs, hu.u'_cont.uL2_eq α hs, clmL2v_toLpCell]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => by
        rw [slicePdIterR_clm_comp L α (hu.u'_cont.hinf hs).smooth]; rfl)
    rw [hd_eq]
    exact ((clmL2v c L).hasFDerivAt.comp_hasDerivAt s (hu.hasDeriv α hs)).congr_of_eventuallyEq hev

/-! ### Convective Operator `bvOp` with Shifted BUC Train Jets -/

/-- Scalar component `y ↦ slicePdIterR γ (dtIterV j (shiftedDriftTrain tr σ) s) y i`. -/
def coeffAt {ν c : ℝ} (tr : B0140.TrainSol ν c) (σ : ℝ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2) (s : ℝ) (y : B0579.Plane) : ℝ :=
  F8Ex.slicePdIterR γ (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) y i

private lemma coeffAt_smooth {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    ContDiff ℝ ∞ (coeffAt tr σ j γ i s) :=
  (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp
    (contDiff_slicePdIterR (dtIterV_shiftedDriftTrain_slice_smooth tr hσ j hs) γ)

private lemma coeffAt_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    Cyl.IsPeriodic c (coeffAt tr σ j γ i s) := by
  intro y
  have hp := periodic_slicePdIterR (dtIterV_shiftedDriftTrain_periodic tr hσ j hs) γ y
  exact congrArg (fun v : Cyl.Vec2 => v i) hp

private lemma coeffAt_pd_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i d : Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    B0579.pd d (coeffAt tr σ j γ i s) = coeffAt tr σ j (Fin.cons d γ) i s := by
  funext y
  have hd : DifferentiableAt ℝ
      (F8Ex.slicePdIterR γ (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s)) y :=
    ((contDiff_slicePdIterR (dtIterV_shiftedDriftTrain_slice_smooth tr hσ j hs) γ).differentiable
      (by simp)) y
  change fderiv ℝ (fun z => F8Ex.slicePdIterR γ (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) z i)
      y (B0579.dir d) =
    F8Ex.slicePdIterR (Fin.cons d γ) (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) y i
  rw [PartI.csb_fderiv_comp_apply hd i (B0579.dir d)]
  rfl

private lemma coeffAt_bdd_on_Icc {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₁₂ : T₁ < T₂) (hT₂ : T₂ < 2)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc T₁ T₂, ∀ y : B0579.Plane, |coeffAt tr σ j γ i s y| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := dtIterV_shiftedDriftTrain_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ j γ
  refine ⟨M, hM0, fun s hs y => ?_⟩
  calc |coeffAt tr σ j γ i s y|
      = ‖F8Ex.slicePdIterR γ (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) y i‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖F8Ex.slicePdIterR γ (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) y‖ :=
        PiLp.norm_apply_le _ i
    _ ≤ M := hM s hs y

private lemma hasDerivAt_coeffAt {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2)
    (y : B0579.Plane) :
    HasDerivAt (fun t => coeffAt tr σ j γ i t y) (coeffAt tr σ (j + 1) γ i s y) s :=
  (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_slicePdIterR_dtIterV tr hσ j γ hs y)

private lemma memLp_bdd_smul {c : ℝ} {ψ : B0579.Plane → ℝ} (hψ_cont : Continuous ψ)
    {B : ℝ} (_hB : 0 ≤ B) (hψ_bdd : ∀ y, |ψ y| ≤ B)
    {f : B0579.Plane → F8Ex.RMerid} (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    MemLp (fun y => ψ y • f y) 2 (F8Ex.cellMeas c) := by
  have hbound : ∀ᵐ y ∂(F8Ex.cellMeas c), ‖ψ y • f y‖ ≤ B * ‖f y‖ :=
    ae_of_all _ fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hψ_bdd y) (norm_nonneg _)
  exact hf.of_le_mul (hψ_cont.aestronglyMeasurable.smul hf.1) hbound

private lemma norm_toLpCell_bdd_smul_le {c : ℝ} {ψ : B0579.Plane → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hψ_bdd : ∀ y, |ψ y| ≤ B)
    {f : B0579.Plane → F8Ex.RMerid} (hf : MemLp f 2 (F8Ex.cellMeas c))
    (hsmul : MemLp (fun y => ψ y • f y) 2 (F8Ex.cellMeas c)) :
    ‖toLpCell hsmul‖ ≤ B * ‖toLpCell hf‖ := by
  have he : ENNReal.ofReal ‖toLpCell hsmul‖ ≤ ENNReal.ofReal (B * ‖toLpCell hf‖) := by
    rw [ofReal_norm_toLpCell, F8Ex.cellL2R]
    have hpt : ∀ y : B0579.Plane, ‖ψ y • f y‖ ≤ ‖B • f y‖ := fun y => by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hB]
      exact mul_le_mul_of_nonneg_right (hψ_bdd y) (norm_nonneg _)
    have hle := eLpNorm_mono hpt (p := 2) (μ := F8Ex.cellMeas c)
    have hrhs : eLpNorm (fun y => B • f y) 2 (F8Ex.cellMeas c) =
        ENNReal.ofReal (B * ‖toLpCell hf‖) := by
      have hmB := hf.const_smul B
      have h1 : F8Ex.cellL2R c (B • f) = ENNReal.ofReal ‖toLpCell hmB‖ :=
        (ofReal_norm_toLpCell hmB).symm
      change F8Ex.cellL2R c (B • f) = _
      rw [h1, toLpCell_smul, norm_smul, Real.norm_of_nonneg hB]
    exact hle.trans_eq hrhs
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (norm_nonneg _))).mp he

private lemma slicePdR_smul_scalar (d : Fin 2) {ψ : B0579.Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {h : B0579.Plane → F8Ex.RMerid} (hh : ContDiff ℝ ∞ h) :
    F8Ex.slicePdR d (fun y => ψ y • h y) =
      (fun y => B0579.pd d ψ y • h y) + (fun y => ψ y • F8Ex.slicePdR d h y) := by
  funext y
  have h1 : DifferentiableAt ℝ ψ y := (hψ.differentiable (by simp)) y
  have h2 : DifferentiableAt ℝ h y := (hh.differentiable (by simp)) y
  change fderiv ℝ (ψ • h) y (B0579.dir d) = _
  rw [fderiv_smul h1 h2]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, B0579.pd]
  rw [add_comm]
  rfl

private lemma coeffAt_mvt_sub {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : T₂ < 2)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2)
    {M₁ : ℝ} (hM₁ : ∀ r ∈ Icc T₁ T₂, ∀ y, |coeffAt tr σ (j + 1) γ i r y| ≤ M₁)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Icc T₁ T₂) (hs : s ∈ Icc T₁ T₂) (y : B0579.Plane) :
    |coeffAt tr σ j γ i s y - coeffAt tr σ j γ i s₀ y| ≤ M₁ * |s - s₀| := by
  have hsub : uIcc s₀ s ⊆ Icc T₁ T₂ := uIcc_subset_Icc hs₀ hs
  have hd : ∀ r ∈ uIcc s₀ s,
      HasDerivWithinAt (fun r => coeffAt tr σ j γ i r y)
        (coeffAt tr σ (j + 1) γ i r y) (uIcc s₀ s) r := by
    intro r hr
    have hrIoo : r ∈ Ioo (0 : ℝ) 2 :=
      ⟨hT₁.trans_le (hsub hr).1, (hsub hr).2.trans_lt hT₂⟩
    exact (hasDerivAt_coeffAt tr hσ j γ i hrIoo y).hasDerivWithinAt
  have hb : ∀ r ∈ uIcc s₀ s, ‖coeffAt tr σ (j + 1) γ i r y‖ ≤ M₁ := by
    intro r hr
    rw [Real.norm_eq_abs]
    exact hM₁ r (hsub hr) y
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_uIcc s₀ s) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hmv

private lemma coeffAt_mvt_taylor {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : T₂ < 2)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2)
    {M₂ : ℝ} (hM₂_nn : 0 ≤ M₂)
    (hM₂ : ∀ r ∈ Icc T₁ T₂, ∀ y, |coeffAt tr σ (j + 2) γ i r y| ≤ M₂)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Icc T₁ T₂) (hs : s ∈ Icc T₁ T₂) (y : B0579.Plane) :
    |coeffAt tr σ j γ i s y - coeffAt tr σ j γ i s₀ y -
        (s - s₀) * coeffAt tr σ (j + 1) γ i s₀ y| ≤ M₂ * |s - s₀| ^ 2 := by
  have hsub : uIcc s₀ s ⊆ Icc T₁ T₂ := uIcc_subset_Icc hs₀ hs
  set c1 := coeffAt tr σ (j + 1) γ i s₀ y
  have hd : ∀ r ∈ uIcc s₀ s,
      HasDerivWithinAt (fun r => coeffAt tr σ j γ i r y - c1 * r)
        (coeffAt tr σ (j + 1) γ i r y - c1) (uIcc s₀ s) r := by
    intro r hr
    have hrIoo : r ∈ Ioo (0 : ℝ) 2 :=
      ⟨hT₁.trans_le (hsub hr).1, (hsub hr).2.trans_lt hT₂⟩
    have h1 : HasDerivWithinAt (fun r => coeffAt tr σ j γ i r y)
        (coeffAt tr σ (j + 1) γ i r y) (uIcc s₀ s) r :=
      (hasDerivAt_coeffAt tr hσ j γ i hrIoo y).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun r => c1 * r) c1 (uIcc s₀ s) r := by
      have h := ((hasDerivAt_id r).const_smul c1).hasDerivWithinAt (s := uIcc s₀ s)
      rwa [smul_eq_mul, mul_one] at h
    exact h1.sub h2
  have hb : ∀ r ∈ uIcc s₀ s,
      ‖coeffAt tr σ (j + 1) γ i r y - c1‖ ≤ M₂ * |s - s₀| := by
    intro r hr
    rw [Real.norm_eq_abs]
    have hm1 := coeffAt_mvt_sub tr hσ hT₁ hT₂ (j + 1) γ i hM₂ hs₀ (hsub hr) y
    have hr_le : |r - s₀| ≤ |s - s₀| := abs_sub_left_of_mem_uIcc hr
    exact hm1.trans (mul_le_mul_of_nonneg_left hr_le hM₂_nn)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_uIcc s₀ s) left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs] at hmv
  have halg : coeffAt tr σ j γ i s y - c1 * s - (coeffAt tr σ j γ i s₀ y - c1 * s₀) =
      coeffAt tr σ j γ i s y - coeffAt tr σ j γ i s₀ y - (s - s₀) * c1 := by ring
  rw [halg] at hmv
  calc |coeffAt tr σ j γ i s y - coeffAt tr σ j γ i s₀ y - (s - s₀) * c1|
      ≤ (M₂ * |s - s₀|) * |s - s₀| := hmv
    _ = M₂ * |s - s₀| ^ 2 := by ring

/-- Inductive `MemLp` and `Cyl.L2v c` continuity of `s ↦ coeffAt tr σ j γ i s • g s` across all
spatial derivative orders `n`. -/
private lemma coeffSmul_mem_and_cont {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ (n : ℕ) (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2)
      {g : ℝ → B0579.Plane → F8Ex.RMerid} (_hg : IsHInfContOn c g) (α : Fin n → Fin 2),
      (∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
        MemLp (F8Ex.slicePdIterR α (fun y => coeffAt tr σ j γ i s y • g s y)) 2 (F8Ex.cellMeas c)) ∧
      ContinuousOn (uL2 c α (fun s y => coeffAt tr σ j γ i s y • g s y)) (Ioo (0 : ℝ) 2)
  | 0, j, _, γ, i, g, hg, α => by
      have hm_s : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
          MemLp (F8Ex.slicePdIterR α (fun y => coeffAt tr σ j γ i s y • g s y))
            2 (F8Ex.cellMeas c) := by
        intro s hs
        let T₁ := s / 2
        let T₂ := (s + 2) / 2
        have hT₁ : 0 < T₁ := by dsimp [T₁]; linarith [hs.1]
        have hT₁₂ : T₁ < T₂ := by dsimp [T₁, T₂]; linarith [hs.2]
        have hT₂ : T₂ < 2 := by dsimp [T₂]; linarith [hs.2]
        have hsIcc : s ∈ Icc T₁ T₂ := ⟨by dsimp [T₁]; linarith [hs.1], by dsimp [T₂]; linarith [hs.2]⟩
        obtain ⟨M₀, hM₀_nn, hM₀⟩ := coeffAt_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ j γ i
        exact memLp_bdd_smul (coeffAt_smooth tr hσ j γ i hs).continuous hM₀_nn (hM₀ s hsIcc)
          ((hg.hinf hs).memL2 0 Fin.elim0)
      refine ⟨hm_s, ?_⟩
      rw [isOpen_Ioo.continuousOn_iff]
      intro s₀ hs₀
      let T₁ := s₀ / 2
      let T₂ := (s₀ + 2) / 2
      have hT₁ : 0 < T₁ := by dsimp [T₁]; linarith [hs₀.1]
      have hT₁₂ : T₁ < T₂ := by dsimp [T₁, T₂]; linarith [hs₀.2]
      have hT₂ : T₂ < 2 := by dsimp [T₂]; linarith [hs₀.2]
      have hs₀Icc : s₀ ∈ Icc T₁ T₂ :=
        ⟨by dsimp [T₁]; linarith [hs₀.1], by dsimp [T₂]; linarith [hs₀.2]⟩
      obtain ⟨M₀, hM₀_nn, hM₀⟩ := coeffAt_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ j γ i
      obtain ⟨M₁, hM₁_nn, hM₁⟩ := coeffAt_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ (j + 1) γ i
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      have hbound_ev : ∀ᶠ s in 𝓝 s₀,
          ‖uL2 c α (fun r y => coeffAt tr σ j γ i r y • g r y) s -
              uL2 c α (fun r y => coeffAt tr σ j γ i r y • g r y) s₀‖ ≤
            M₀ * ‖uL2 c Fin.elim0 g s - uL2 c Fin.elim0 g s₀‖ +
              (M₁ * ‖uL2 c Fin.elim0 g s₀‖) * |s - s₀| := by
        have hnhds : Ioo T₁ T₂ ∈ 𝓝 s₀ :=
          isOpen_Ioo.mem_nhds ⟨by dsimp [T₁]; linarith [hs₀.1], by dsimp [T₂]; linarith [hs₀.2]⟩
        filter_upwards [hnhds] with s hs_in
        have hsIcc : s ∈ Icc T₁ T₂ := ⟨hs_in.1.le, hs_in.2.le⟩
        have hsIoo : s ∈ Ioo (0 : ℝ) 2 := ⟨hT₁.trans_le hsIcc.1, hsIcc.2.trans_lt hT₂⟩
        have hm1 : MemLp (fun y => coeffAt tr σ j γ i s y • (g s y - g s₀ y))
            2 (F8Ex.cellMeas c) :=
          memLp_bdd_smul (coeffAt_smooth tr hσ j γ i hsIoo).continuous hM₀_nn (hM₀ s hsIcc)
            (((hg.hinf hsIoo).memL2 0 Fin.elim0).sub ((hg.hinf hs₀).memL2 0 Fin.elim0))
        have hm2 : MemLp (fun y => (coeffAt tr σ j γ i s y - coeffAt tr σ j γ i s₀ y) • g s₀ y)
            2 (F8Ex.cellMeas c) :=
          memLp_bdd_smul
            ((coeffAt_smooth tr hσ j γ i hsIoo).continuous.sub
              (coeffAt_smooth tr hσ j γ i hs₀).continuous)
            (mul_nonneg hM₁_nn (abs_nonneg _))
            (fun y => coeffAt_mvt_sub tr hσ hT₁ hT₂ j γ i hM₁ hs₀Icc hsIcc y)
            ((hg.hinf hs₀).memL2 0 Fin.elim0)
        have hdecomp : uL2 c α (fun r y => coeffAt tr σ j γ i r y • g r y) s -
            uL2 c α (fun r y => coeffAt tr σ j γ i r y • g r y) s₀ =
            toLpCell hm1 + toLpCell hm2 := by
          rw [uL2_eq_toLpCell α (hm_s hsIoo), uL2_eq_toLpCell α (hm_s hs₀),
            ← toLpCell_sub, ← toLpCell_add]
          refine toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_)
          simp only [F8Ex.slicePdIterR, Pi.sub_apply, Pi.add_apply, smul_sub, sub_smul]
          abel
        have hb1 : ‖toLpCell hm1‖ ≤ M₀ * ‖uL2 c Fin.elim0 g s - uL2 c Fin.elim0 g s₀‖ := by
          have h := norm_toLpCell_bdd_smul_le hM₀_nn (hM₀ s hsIcc)
            (((hg.hinf hsIoo).memL2 0 Fin.elim0).sub ((hg.hinf hs₀).memL2 0 Fin.elim0)) hm1
          rw [toLpCell_sub ((hg.hinf hsIoo).memL2 0 Fin.elim0) ((hg.hinf hs₀).memL2 0 Fin.elim0),
            ← hg.uL2_eq Fin.elim0 hsIoo, ← hg.uL2_eq Fin.elim0 hs₀] at h
          exact h
        have hb2 : ‖toLpCell hm2‖ ≤ (M₁ * ‖uL2 c Fin.elim0 g s₀‖) * |s - s₀| := by
          have h := norm_toLpCell_bdd_smul_le (mul_nonneg hM₁_nn (abs_nonneg _))
            (fun y => coeffAt_mvt_sub tr hσ hT₁ hT₂ j γ i hM₁ hs₀Icc hsIcc y)
            ((hg.hinf hs₀).memL2 0 Fin.elim0) hm2
          rw [← hg.uL2_eq Fin.elim0 hs₀] at h
          exact h.trans_eq (by ring)
        rw [hdecomp]
        exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
      have htend_rhs : Tendsto (fun s => M₀ * ‖uL2 c Fin.elim0 g s - uL2 c Fin.elim0 g s₀‖ +
          (M₁ * ‖uL2 c Fin.elim0 g s₀‖) * |s - s₀|) (𝓝 s₀) (𝓝 0) := by
        have ht1 : Tendsto (fun s => M₀ * ‖uL2 c Fin.elim0 g s - uL2 c Fin.elim0 g s₀‖)
            (𝓝 s₀) (𝓝 (M₀ * 0)) :=
          ((tendsto_iff_norm_sub_tendsto_zero.mp (hg.continuousAt Fin.elim0 hs₀)).const_mul M₀)
        have ht2 : Tendsto (fun s => (M₁ * ‖uL2 c Fin.elim0 g s₀‖) * |s - s₀|)
            (𝓝 s₀) (𝓝 ((M₁ * ‖uL2 c Fin.elim0 g s₀‖) * 0)) := by
          have habs : ContinuousAt (fun s : ℝ => |s - s₀|) s₀ :=
            (continuousAt_id.sub continuousAt_const).abs
          have ht0 : Tendsto (fun s : ℝ => |s - s₀|) (𝓝 s₀) (𝓝 0) := by
            simpa using habs.tendsto
          exact ht0.const_mul _
        simpa using ht1.add ht2
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound_ev htend_rhs
  | n + 1, j, _, γ, i, g, hg, α => by
      obtain ⟨β, d, rfl⟩ := exists_snocIdx α
      obtain ⟨hm1, hc1⟩ := coeffSmul_mem_and_cont hc hν tr hbuc hσ n j (Fin.cons d γ) i hg β
      obtain ⟨hm2, hc2⟩ := coeffSmul_mem_and_cont hc hν tr hbuc hσ n j γ i (hg.slicePdR d) β
      have hfun_eq : ∀ {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2),
          F8Ex.slicePdIterR (snocIdx β d) (fun y => coeffAt tr σ j γ i s y • g s y) =
            F8Ex.slicePdIterR β (fun y => coeffAt tr σ j (Fin.cons d γ) i s y • g s y) +
              F8Ex.slicePdIterR β (fun y => coeffAt tr σ j γ i s y • F8Ex.slicePdR d (g s) y) := by
        intro s hs
        have hsm_c := coeffAt_smooth tr hσ j γ i hs
        have hsm_cd := coeffAt_smooth tr hσ j (Fin.cons d γ) i hs
        have hsm_g := (hg.hinf hs).smooth
        have hsm_1 : ContDiff ℝ ∞ (fun y => coeffAt tr σ j (Fin.cons d γ) i s y • g s y) :=
          hsm_cd.smul hsm_g
        have hsm_2 : ContDiff ℝ ∞ (fun y => coeffAt tr σ j γ i s y • F8Ex.slicePdR d (g s) y) :=
          hsm_c.smul (contDiff_slicePdR hsm_g d)
        rw [← slicePdIterR_slicePdR, slicePdR_smul_scalar d hsm_c hsm_g, coeffAt_pd_eq tr hσ j γ i d hs]
        exact slicePdIterR_add hsm_1 hsm_2 β
      have hm_all : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
          MemLp (F8Ex.slicePdIterR (snocIdx β d) (fun y => coeffAt tr σ j γ i s y • g s y))
            2 (F8Ex.cellMeas c) := by
        intro s hs
        rw [hfun_eq hs]
        exact (hm1 hs).add (hm2 hs)
      refine ⟨hm_all, (hc1.add hc2).congr fun s hs => ?_⟩
      dsimp only [Pi.add_apply]
      rw [uL2_eq_toLpCell (snocIdx β d) (hm_all hs),
        uL2_eq_toLpCell β (hm1 hs), uL2_eq_toLpCell β (hm2 hs), ← toLpCell_add]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => congrFun (hfun_eq hs) y)

lemma IsHInfContOn.coeffSmul {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2)
    {g : ℝ → B0579.Plane → F8Ex.RMerid} (hg : IsHInfContOn c g) :
    IsHInfContOn c (fun s y => coeffAt tr σ j γ i s y • g s y) where
  hinf {s} hs :=
    { smooth := (coeffAt_smooth tr hσ j γ i hs).smul (hg.hinf hs).smooth
      periodic := fun z => by
        show coeffAt tr σ j γ i s (z.1 + c, z.2) • g s (z.1 + c, z.2) = _
        rw [coeffAt_periodic tr hσ j γ i hs z, (hg.hinf hs).periodic z]
      memL2 := fun n α => (coeffSmul_mem_and_cont hc hν tr hbuc hσ n j γ i hg α).1 hs }
  cont {n} α := (coeffSmul_mem_and_cont hc hν tr hbuc hσ n j γ i hg α).2

/-- Inductive `Cyl.L2v c` time-differentiability of `s ↦ coeffAt tr σ j γ i s • g s` across all
spatial derivative orders `n`. -/
private lemma coeffSmul_hasDeriv {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ (n : ℕ) (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2)
      {g g' : ℝ → B0579.Plane → F8Ex.RMerid} (_hg : HasHInfDerivOn c g g')
      (α : Fin n → Fin 2) {s₀ : ℝ} (_hs₀ : s₀ ∈ Ioo (0 : ℝ) 2),
      HasDerivAt (uL2 c α (fun s y => coeffAt tr σ j γ i s y • g s y))
        (uL2 c α (fun s y =>
          coeffAt tr σ (j + 1) γ i s y • g s y + coeffAt tr σ j γ i s y • g' s y) s₀) s₀
  | 0, j, _, γ, i, g, g', hg, α, s₀, hs₀ => by
      let T₁ := s₀ / 2
      let T₂ := (s₀ + 2) / 2
      have hT₁ : 0 < T₁ := by dsimp [T₁]; linarith [hs₀.1]
      have hT₁₂ : T₁ < T₂ := by dsimp [T₁, T₂]; linarith [hs₀.2]
      have hT₂ : T₂ < 2 := by dsimp [T₂]; linarith [hs₀.2]
      have hs₀Icc : s₀ ∈ Icc T₁ T₂ :=
        ⟨by dsimp [T₁]; linarith [hs₀.1], by dsimp [T₂]; linarith [hs₀.2]⟩
      obtain ⟨M₀, hM₀_nn, hM₀⟩ := coeffAt_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ j γ i
      obtain ⟨M₁, hM₁_nn, hM₁⟩ := coeffAt_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ (j + 1) γ i
      obtain ⟨M₂, hM₂_nn, hM₂⟩ := coeffAt_bdd_on_Icc hc hν tr hbuc hσ hT₁ hT₁₂ hT₂ (j + 2) γ i
      have hcont_fg := hg.u_cont.coeffSmul hc hν tr hbuc hσ j γ i
      have hcont_out : IsHInfContOn c
          (fun s y => coeffAt tr σ (j + 1) γ i s y • g s y + coeffAt tr σ j γ i s y • g' s y) :=
        (hg.u_cont.coeffSmul hc hν tr hbuc hσ (j + 1) γ i).add
          (hg.u'_cont.coeffSmul hc hν tr hbuc hσ j γ i)
      rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
      intro ε hε
      set K : ℝ := M₀ + M₁ + M₂ * ‖uL2 c Fin.elim0 g s₀‖ + 1
      have hK_pos : 0 < K := by dsimp [K]; positivity
      have hd_g := hg.hasDeriv Fin.elim0 hs₀
      rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hd_g
      have hev_g1 : ∀ᶠ h : ℝ in 𝓝 0,
          ‖uL2 c Fin.elim0 g (s₀ + h) - uL2 c Fin.elim0 g s₀ -
              h • uL2 c Fin.elim0 g' s₀‖ ≤ (ε / (3 * K)) * ‖h‖ :=
        hd_g (div_pos hε (by positivity))
      have hev_g2 : ∀ᶠ h : ℝ in 𝓝 0,
          ‖uL2 c Fin.elim0 g (s₀ + h) - uL2 c Fin.elim0 g s₀‖ ≤ ε / (3 * K) := by
        have htend := tendsto_iff_norm_sub_tendsto_zero.mp (hg.u_cont.continuousAt Fin.elim0 hs₀)
        have hcomp : Tendsto (fun h : ℝ => ‖uL2 c Fin.elim0 g (s₀ + h) - uL2 c Fin.elim0 g s₀‖)
            (𝓝 0) (𝓝 0) := by
          have hc_sh : ContinuousAt (fun h : ℝ => s₀ + h) 0 := continuousAt_const.add continuousAt_id
          have ht_sh : Tendsto (fun h : ℝ => s₀ + h) (𝓝 0) (𝓝 s₀) := by
            simpa using hc_sh.tendsto
          exact htend.comp ht_sh
        exact (hcomp.eventually (gt_mem_nhds (div_pos hε (by positivity)))).mono fun _ hh => hh.le
      have hev_h : ∀ᶠ h : ℝ in 𝓝 0, |h| ≤ ε / (3 * K) ∧ s₀ + h ∈ Ioo T₁ T₂ := by
        have h1 : ∀ᶠ h : ℝ in 𝓝 0, |h| < ε / (3 * K) := by
          have hc_abs : ContinuousAt (fun h : ℝ => |h|) 0 := continuous_abs.continuousAt
          have ht_abs : Tendsto (fun h : ℝ => |h|) (𝓝 0) (𝓝 0) := by
            simpa using hc_abs.tendsto
          exact ht_abs.eventually (gt_mem_nhds (div_pos hε (by positivity)))
        have h2 : ∀ᶠ h : ℝ in 𝓝 0, s₀ + h ∈ Ioo T₁ T₂ := by
          have hc_sh : ContinuousAt (fun h : ℝ => s₀ + h) 0 := continuousAt_const.add continuousAt_id
          have hmem0 : s₀ + (0 : ℝ) ∈ Ioo T₁ T₂ := by
            simp only [add_zero]
            exact ⟨by dsimp [T₁]; linarith [hs₀.1], by dsimp [T₂]; linarith [hs₀.2]⟩
          exact hc_sh.eventually (isOpen_Ioo.mem_nhds hmem0)
        exact (h1.and h2).mono fun _ hh => ⟨hh.1.le, hh.2⟩
      filter_upwards [hev_g1, hev_g2, hev_h] with h hg1 hg2 ⟨hh_le, hsh_in⟩
      have hshIcc : s₀ + h ∈ Icc T₁ T₂ := ⟨hsh_in.1.le, hsh_in.2.le⟩
      have hshIoo : s₀ + h ∈ Ioo (0 : ℝ) 2 := ⟨hT₁.trans_le hshIcc.1, hshIcc.2.trans_lt hT₂⟩
      have hm_g_sh := (hg.u_cont.hinf hshIoo).memL2 0 Fin.elim0
      have hm_g_s₀ := (hg.u_cont.hinf hs₀).memL2 0 Fin.elim0
      have hm_g'_s₀ := (hg.u'_cont.hinf hs₀).memL2 0 Fin.elim0
      have hm_A : MemLp
          (fun y => coeffAt tr σ j γ i s₀ y • (g (s₀ + h) y - g s₀ y - h • g' s₀ y))
          2 (F8Ex.cellMeas c) :=
        memLp_bdd_smul (coeffAt_smooth tr hσ j γ i hs₀).continuous hM₀_nn (hM₀ s₀ hs₀Icc)
          ((hm_g_sh.sub hm_g_s₀).sub (hm_g'_s₀.const_smul h))
      have hm_B : MemLp
          (fun y => (coeffAt tr σ j γ i (s₀ + h) y - coeffAt tr σ j γ i s₀ y) •
            (g (s₀ + h) y - g s₀ y)) 2 (F8Ex.cellMeas c) :=
        memLp_bdd_smul (ψ := fun y => coeffAt tr σ j γ i (s₀ + h) y - coeffAt tr σ j γ i s₀ y)
          ((coeffAt_smooth tr hσ j γ i hshIoo).continuous.sub
            (coeffAt_smooth tr hσ j γ i hs₀).continuous)
          (mul_nonneg hM₁_nn (abs_nonneg _))
          (fun y => by
            have hm := coeffAt_mvt_sub tr hσ hT₁ hT₂ j γ i hM₁ hs₀Icc hshIcc y
            simpa only [add_sub_cancel_left] using hm)
          (hm_g_sh.sub hm_g_s₀)
      have hm_C : MemLp
          (fun y => (coeffAt tr σ j γ i (s₀ + h) y - coeffAt tr σ j γ i s₀ y -
            h * coeffAt tr σ (j + 1) γ i s₀ y) • g s₀ y) 2 (F8Ex.cellMeas c) :=
        memLp_bdd_smul
          (ψ := fun y => coeffAt tr σ j γ i (s₀ + h) y - coeffAt tr σ j γ i s₀ y -
            h * coeffAt tr σ (j + 1) γ i s₀ y)
          (((coeffAt_smooth tr hσ j γ i hshIoo).continuous.sub
            (coeffAt_smooth tr hσ j γ i hs₀).continuous).sub
            (continuous_const.mul (coeffAt_smooth tr hσ (j + 1) γ i hs₀).continuous))
          (mul_nonneg hM₂_nn (sq_nonneg |h|))
          (fun y => by
            have hm := coeffAt_mvt_taylor tr hσ hT₁ hT₂ j γ i hM₂_nn hM₂ hs₀Icc hshIcc y
            simpa only [add_sub_cancel_left] using hm)
          hm_g_s₀
      have hrem_eq :
          uL2 c α (fun s y => coeffAt tr σ j γ i s y • g s y) (s₀ + h) -
            uL2 c α (fun s y => coeffAt tr σ j γ i s y • g s y) s₀ -
            h • uL2 c α (fun s y =>
              coeffAt tr σ (j + 1) γ i s y • g s y + coeffAt tr σ j γ i s y • g' s y) s₀ =
          toLpCell hm_A + toLpCell hm_B + toLpCell hm_C := by
        rw [hcont_fg.uL2_eq α hshIoo, hcont_fg.uL2_eq α hs₀, hcont_out.uL2_eq α hs₀,
          ← toLpCell_smul, ← toLpCell_sub, ← toLpCell_sub, ← toLpCell_add, ← toLpCell_add]
        refine toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_)
        simp only [F8Ex.slicePdIterR, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
          smul_add, smul_sub, sub_smul, mul_smul]
        rw [smul_comm (coeffAt tr σ j γ i s₀ y) h (g' s₀ y)]
        abel
      have hbA : ‖toLpCell hm_A‖ ≤ (ε / 3) * ‖h‖ := by
        have h1 := norm_toLpCell_bdd_smul_le hM₀_nn (hM₀ s₀ hs₀Icc)
          ((hm_g_sh.sub hm_g_s₀).sub (hm_g'_s₀.const_smul h)) hm_A
        rw [toLpCell_sub (hm_g_sh.sub hm_g_s₀) (hm_g'_s₀.const_smul h),
          toLpCell_sub hm_g_sh hm_g_s₀, toLpCell_smul h hm_g'_s₀,
          ← hg.u_cont.uL2_eq Fin.elim0 hshIoo, ← hg.u_cont.uL2_eq Fin.elim0 hs₀,
          ← hg.u'_cont.uL2_eq Fin.elim0 hs₀] at h1
        have hM₀_le : M₀ ≤ K := by
          dsimp [K]
          have : 0 ≤ M₂ * ‖uL2 c Fin.elim0 g s₀‖ := mul_nonneg hM₂_nn (norm_nonneg _)
          linarith
        calc ‖toLpCell hm_A‖
            ≤ M₀ * ((ε / (3 * K)) * ‖h‖) := h1.trans (mul_le_mul_of_nonneg_left hg1 hM₀_nn)
          _ ≤ K * ((ε / (3 * K)) * ‖h‖) :=
              mul_le_mul_of_nonneg_right hM₀_le (mul_nonneg (div_nonneg hε.le (by positivity)) (norm_nonneg _))
          _ = (ε / 3) * ‖h‖ := by field_simp [hK_pos.ne']
      have hbB : ‖toLpCell hm_B‖ ≤ (ε / 3) * ‖h‖ := by
        have h1 := norm_toLpCell_bdd_smul_le (mul_nonneg hM₁_nn (abs_nonneg h))
          (fun y => by
            have hm := coeffAt_mvt_sub tr hσ hT₁ hT₂ j γ i hM₁ hs₀Icc hshIcc y
            simpa only [add_sub_cancel_left] using hm)
          (hm_g_sh.sub hm_g_s₀)
          hm_B
        rw [toLpCell_sub hm_g_sh hm_g_s₀, ← hg.u_cont.uL2_eq Fin.elim0 hshIoo,
          ← hg.u_cont.uL2_eq Fin.elim0 hs₀] at h1
        have hM₁_le : M₁ ≤ K := by
          dsimp [K]
          have : 0 ≤ M₂ * ‖uL2 c Fin.elim0 g s₀‖ := mul_nonneg hM₂_nn (norm_nonneg _)
          linarith
        calc ‖toLpCell hm_B‖
            ≤ (M₁ * |h|) * (ε / (3 * K)) :=
              h1.trans (mul_le_mul_of_nonneg_left hg2 (mul_nonneg hM₁_nn (abs_nonneg h)))
          _ = M₁ * ((ε / (3 * K)) * ‖h‖) := by rw [Real.norm_eq_abs]; ring
          _ ≤ K * ((ε / (3 * K)) * ‖h‖) :=
              mul_le_mul_of_nonneg_right hM₁_le (mul_nonneg (div_nonneg hε.le (by positivity)) (norm_nonneg _))
          _ = (ε / 3) * ‖h‖ := by field_simp [hK_pos.ne']
      have hbC : ‖toLpCell hm_C‖ ≤ (ε / 3) * ‖h‖ := by
        have h1 := norm_toLpCell_bdd_smul_le (mul_nonneg hM₂_nn (sq_nonneg |h|))
          (fun y => by
            have hm := coeffAt_mvt_taylor tr hσ hT₁ hT₂ j γ i hM₂_nn hM₂ hs₀Icc hshIcc y
            simpa only [add_sub_cancel_left] using hm)
          hm_g_s₀ hm_C
        rw [← hg.u_cont.uL2_eq Fin.elim0 hs₀] at h1
        have hM₂_le : M₂ * ‖uL2 c Fin.elim0 g s₀‖ ≤ K := by dsimp [K]; linarith
        calc ‖toLpCell hm_C‖
            ≤ (M₂ * ‖uL2 c Fin.elim0 g s₀‖) * (|h| * |h|) := by
              refine h1.trans_eq ?_
              ring
          _ ≤ K * ((ε / (3 * K)) * ‖h‖) := by
              rw [Real.norm_eq_abs]
              exact mul_le_mul hM₂_le (mul_le_mul_of_nonneg_right hh_le (abs_nonneg h))
                (mul_nonneg (abs_nonneg h) (abs_nonneg h)) hK_pos.le
          _ = (ε / 3) * ‖h‖ := by field_simp [hK_pos.ne']
      rw [hrem_eq]
      calc ‖toLpCell hm_A + toLpCell hm_B + toLpCell hm_C‖
          ≤ ‖toLpCell hm_A‖ + ‖toLpCell hm_B‖ + ‖toLpCell hm_C‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (ε / 3) * ‖h‖ + (ε / 3) * ‖h‖ + (ε / 3) * ‖h‖ :=
            add_le_add (add_le_add hbA hbB) hbC
        _ = ε * ‖h‖ := by ring
  | n + 1, j, _, γ, i, g, g', hg, α, s₀, hs₀ => by
      obtain ⟨β, d, rfl⟩ := exists_snocIdx α
      have hd1 := coeffSmul_hasDeriv hc hν tr hbuc hσ n j (Fin.cons d γ) i hg β hs₀
      have hd2 := coeffSmul_hasDeriv hc hν tr hbuc hσ n j γ i (hg.slicePdR d) β hs₀
      have hcont_cur := hg.u_cont.coeffSmul hc hν tr hbuc hσ j γ i
      have hcont_1 := hg.u_cont.coeffSmul hc hν tr hbuc hσ j (Fin.cons d γ) i
      have hcont_2 := (hg.u_cont.slicePdR d).coeffSmul hc hν tr hbuc hσ j γ i
      have hcont_out : IsHInfContOn c
          (fun s y => coeffAt tr σ (j + 1) γ i s y • g s y + coeffAt tr σ j γ i s y • g' s y) :=
        (hg.u_cont.coeffSmul hc hν tr hbuc hσ (j + 1) γ i).add
          (hg.u'_cont.coeffSmul hc hν tr hbuc hσ j γ i)
      have hcont_out1 : IsHInfContOn c
          (fun s y => coeffAt tr σ (j + 1) (Fin.cons d γ) i s y • g s y +
            coeffAt tr σ j (Fin.cons d γ) i s y • g' s y) :=
        (hg.u_cont.coeffSmul hc hν tr hbuc hσ (j + 1) (Fin.cons d γ) i).add
          (hg.u'_cont.coeffSmul hc hν tr hbuc hσ j (Fin.cons d γ) i)
      have hcont_out2 : IsHInfContOn c
          (fun s y => coeffAt tr σ (j + 1) γ i s y • F8Ex.slicePdR d (g s) y +
            coeffAt tr σ j γ i s y • F8Ex.slicePdR d (g' s) y) :=
        ((hg.u_cont.slicePdR d).coeffSmul hc hν tr hbuc hσ (j + 1) γ i).add
          ((hg.u'_cont.slicePdR d).coeffSmul hc hν tr hbuc hσ j γ i)
      have hev : uL2 c (snocIdx β d) (fun s y => coeffAt tr σ j γ i s y • g s y) =ᶠ[𝓝 s₀]
          fun s => uL2 c β (fun r y => coeffAt tr σ j (Fin.cons d γ) i r y • g r y) s +
            uL2 c β (fun r y => coeffAt tr σ j γ i r y • F8Ex.slicePdR d (g r) y) s := by
        filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
        rw [hcont_cur.uL2_eq (snocIdx β d) hs, hcont_1.uL2_eq β hs, hcont_2.uL2_eq β hs,
          ← toLpCell_add]
        refine toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_)
        have hsm_c := coeffAt_smooth tr hσ j γ i hs
        have hsm_cd := coeffAt_smooth tr hσ j (Fin.cons d γ) i hs
        have hsm_g := (hg.u_cont.hinf hs).smooth
        have hsm_1 : ContDiff ℝ ∞ (fun z => coeffAt tr σ j (Fin.cons d γ) i s z • g s z) :=
          hsm_cd.smul hsm_g
        have hsm_2 : ContDiff ℝ ∞ (fun z => coeffAt tr σ j γ i s z • F8Ex.slicePdR d (g s) z) :=
          hsm_c.smul (contDiff_slicePdR hsm_g d)
        rw [← slicePdIterR_slicePdR, slicePdR_smul_scalar d hsm_c hsm_g,
          coeffAt_pd_eq tr hσ j γ i d hs, slicePdIterR_add hsm_1 hsm_2 β]
      have hd_eq : uL2 c (snocIdx β d)
          (fun s y => coeffAt tr σ (j + 1) γ i s y • g s y + coeffAt tr σ j γ i s y • g' s y) s₀ =
          uL2 c β (fun s y => coeffAt tr σ (j + 1) (Fin.cons d γ) i s y • g s y +
            coeffAt tr σ j (Fin.cons d γ) i s y • g' s y) s₀ +
          uL2 c β (fun s y => coeffAt tr σ (j + 1) γ i s y • F8Ex.slicePdR d (g s) y +
            coeffAt tr σ j γ i s y • F8Ex.slicePdR d (g' s) y) s₀ := by
        rw [hcont_out.uL2_eq (snocIdx β d) hs₀, hcont_out1.uL2_eq β hs₀, hcont_out2.uL2_eq β hs₀,
          ← toLpCell_add]
        refine toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_)
        have hsm_c := coeffAt_smooth tr hσ j γ i hs₀
        have hsm_c1 := coeffAt_smooth tr hσ (j + 1) γ i hs₀
        have hsm_cd := coeffAt_smooth tr hσ j (Fin.cons d γ) i hs₀
        have hsm_c1d := coeffAt_smooth tr hσ (j + 1) (Fin.cons d γ) i hs₀
        have hsm_g := (hg.u_cont.hinf hs₀).smooth
        have hsm_g' := (hg.u'_cont.hinf hs₀).smooth
        rw [← slicePdIterR_slicePdR]
        have hsm_p1 : ContDiff ℝ ∞ (fun z => coeffAt tr σ (j + 1) γ i s₀ z • g s₀ z) :=
          hsm_c1.smul hsm_g
        have hsm_p2 : ContDiff ℝ ∞ (fun z => coeffAt tr σ j γ i s₀ z • g' s₀ z) :=
          hsm_c.smul hsm_g'
        have hsm_q1 : ContDiff ℝ ∞
            (fun z => coeffAt tr σ (j + 1) (Fin.cons d γ) i s₀ z • g s₀ z +
              coeffAt tr σ j (Fin.cons d γ) i s₀ z • g' s₀ z) :=
          (hsm_c1d.smul hsm_g).add (hsm_cd.smul hsm_g')
        have hsm_q2 : ContDiff ℝ ∞
            (fun z => coeffAt tr σ (j + 1) γ i s₀ z • F8Ex.slicePdR d (g s₀) z +
              coeffAt tr σ j γ i s₀ z • F8Ex.slicePdR d (g' s₀) z) :=
          (hsm_c1.smul (contDiff_slicePdR hsm_g d)).add
            (hsm_c.smul (contDiff_slicePdR hsm_g' d))
        have hpd_sum : F8Ex.slicePdR d
            (fun z => coeffAt tr σ (j + 1) γ i s₀ z • g s₀ z + coeffAt tr σ j γ i s₀ z • g' s₀ z) =
            ((fun z => coeffAt tr σ (j + 1) (Fin.cons d γ) i s₀ z • g s₀ z +
                coeffAt tr σ j (Fin.cons d γ) i s₀ z • g' s₀ z) +
              (fun z => coeffAt tr σ (j + 1) γ i s₀ z • F8Ex.slicePdR d (g s₀) z +
                coeffAt tr σ j γ i s₀ z • F8Ex.slicePdR d (g' s₀) z)) := by
          change F8Ex.slicePdR d
              ((fun z => coeffAt tr σ (j + 1) γ i s₀ z • g s₀ z) +
                (fun z => coeffAt tr σ j γ i s₀ z • g' s₀ z)) = _
          rw [slicePdR_add hsm_p1 hsm_p2 d,
            slicePdR_smul_scalar d hsm_c1 hsm_g, slicePdR_smul_scalar d hsm_c hsm_g',
            coeffAt_pd_eq tr hσ (j + 1) γ i d hs₀, coeffAt_pd_eq tr hσ j γ i d hs₀]
          funext z
          simp only [Pi.add_apply]
          abel
        rw [hpd_sum, slicePdIterR_add hsm_q1 hsm_q2 β]
      rw [hd_eq]
      exact (hd1.add hd2).congr_of_eventuallyEq hev

lemma HasHInfDerivOn.coeffSmul {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {m : ℕ} (γ : Fin m → Fin 2) (i : Fin 2)
    {g g' : ℝ → B0579.Plane → F8Ex.RMerid} (hg : HasHInfDerivOn c g g') :
    HasHInfDerivOn c
      (fun s y => coeffAt tr σ j γ i s y • g s y)
      (fun s y => coeffAt tr σ (j + 1) γ i s y • g s y + coeffAt tr σ j γ i s y • g' s y) where
  u_cont := hg.u_cont.coeffSmul hc hν tr hbuc hσ j γ i
  u'_cont := (hg.u_cont.coeffSmul hc hν tr hbuc hσ (j + 1) γ i).add
    (hg.u'_cont.coeffSmul hc hν tr hbuc hσ j γ i)
  hasDeriv {n} α {_} hs := coeffSmul_hasDeriv hc hν tr hbuc hσ n j γ i hg α hs

/-- Unprojected convective-stretching slice operator `B_v f = realBvSlice v f (∂_q f) (∂_η f)`. -/
def bvOp (v f : B0579.Plane → F8Ex.RMerid) : B0579.Plane → F8Ex.RMerid :=
  F8Ex.realBvSlice v f (F8Ex.slicePdR 0 f) (F8Ex.slicePdR 1 f)

private lemma bvOp_dtIterV_eq_sum {ν c : ℝ} (tr : B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) (f : B0579.Plane → F8Ex.RMerid) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    bvOp (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) f =
      ((fun y => coeffAt tr σ j Fin.elim0 0 s y • F8Ex.slicePdR 0 f y) +
        (fun y => coeffAt tr σ j Fin.elim0 1 s y • F8Ex.slicePdR 1 f y)) +
      (((fun y => coeffAt tr σ j ![0] 0 s y • coordMap 0 0 (f y)) +
          (fun y => coeffAt tr σ j ![0] 1 s y • coordMap 0 1 (f y))) +
        ((fun y => coeffAt tr σ j ![1] 0 s y • coordMap 1 0 (f y)) +
          (fun y => coeffAt tr σ j ![1] 1 s y • coordMap 1 1 (f y)))) := by
  funext y
  have hd : DifferentiableAt ℝ (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) y :=
    ((dtIterV_shiftedDriftTrain_slice_smooth tr hσ j hs).differentiable (by simp)) y
  have hq : ∀ l : Fin 2,
      fderiv ℝ (fun z => dtIterV j (F8Ex.shiftedDriftTrain tr σ) s z l) y ((1 : ℝ), (0 : ℝ)) =
        coeffAt tr σ j ![0] l s y := by
    intro l
    rw [PartI.csb_fderiv_comp_apply hd l ((1 : ℝ), (0 : ℝ))]
    rfl
  have he : ∀ l : Fin 2,
      fderiv ℝ (fun z => dtIterV j (F8Ex.shiftedDriftTrain tr σ) s z l) y ((0 : ℝ), (1 : ℝ)) =
        coeffAt tr σ j ![1] l s y := by
    intro l
    rw [PartI.csb_fderiv_comp_apply hd l ((0 : ℝ), (1 : ℝ))]
    rfl
  ext l
  revert l
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
    simp only [bvOp, F8Ex.realBvSlice, PiLp.toLp_apply, hq, he, coeffAt, F8Ex.slicePdIterR,
      Pi.add_apply, PiLp.add_apply, PiLp.smul_apply, coordMap_apply,
      eVec_zero_zero, eVec_zero_one, eVec_one_zero, eVec_one_one, smul_eq_mul] <;>
    ring

private lemma isHInfContOn_congr {c : ℝ} {u v : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : IsHInfContOn c u) (h : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 → u s = v s) :
    IsHInfContOn c v where
  hinf {_} hs := h hs ▸ hu.hinf hs
  cont α := (hu.cont α).congr fun _ hs => uL2_congr_slice α (h hs).symm

private lemma hasHInfDerivOn_congr {c : ℝ}
    {u u' v v' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hu : HasHInfDerivOn c u u')
    (h1 : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 → u s = v s)
    (h2 : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 → u' s = v' s) :
    HasHInfDerivOn c v v' where
  u_cont := isHInfContOn_congr hu.u_cont h1
  u'_cont := isHInfContOn_congr hu.u'_cont h2
  hasDeriv {n} α {s} hs := by
    have hev : uL2 c α v =ᶠ[𝓝 s] uL2 c α u := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact uL2_congr_slice α (h1 ht).symm
    rw [← uL2_congr_slice α (h2 hs)]
    exact (hu.hasDeriv α hs).congr_of_eventuallyEq hev

lemma IsHInfContOn.bvOp_dtIterV {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {u : ℝ → B0579.Plane → F8Ex.RMerid} (hu : IsHInfContOn c u) :
    IsHInfContOn c (fun s => bvOp (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) (u s)) := by
  have hsum :=
    (((hu.slicePdR 0).coeffSmul hc hν tr hbuc hσ j Fin.elim0 0).add
      ((hu.slicePdR 1).coeffSmul hc hν tr hbuc hσ j Fin.elim0 1)).add
    (((((hu.clm_comp (coordMap 0 0)).coeffSmul hc hν tr hbuc hσ j ![0] 0).add
        ((hu.clm_comp (coordMap 0 1)).coeffSmul hc hν tr hbuc hσ j ![0] 1))).add
      (((hu.clm_comp (coordMap 1 0)).coeffSmul hc hν tr hbuc hσ j ![1] 0).add
        ((hu.clm_comp (coordMap 1 1)).coeffSmul hc hν tr hbuc hσ j ![1] 1)))
  exact isHInfContOn_congr hsum fun {s} hs => (bvOp_dtIterV_eq_sum tr hσ j (u s) hs).symm

lemma HasHInfDerivOn.bvOp_dtIterV {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    (j : ℕ) {u u' : ℝ → B0579.Plane → F8Ex.RMerid} (hu : HasHInfDerivOn c u u') :
    HasHInfDerivOn c
      (fun s => bvOp (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) (u s))
      (fun s => bvOp (dtIterV (j + 1) (F8Ex.shiftedDriftTrain tr σ) s) (u s) +
        bvOp (dtIterV j (F8Ex.shiftedDriftTrain tr σ) s) (u' s)) := by
  have hd_sum :=
    (((hu.slicePdR 0).coeffSmul hc hν tr hbuc hσ j Fin.elim0 0).add
      ((hu.slicePdR 1).coeffSmul hc hν tr hbuc hσ j Fin.elim0 1)).add
    (((((hu.clm_comp (coordMap 0 0)).coeffSmul hc hν tr hbuc hσ j ![0] 0).add
        ((hu.clm_comp (coordMap 0 1)).coeffSmul hc hν tr hbuc hσ j ![0] 1))).add
      (((hu.clm_comp (coordMap 1 0)).coeffSmul hc hν tr hbuc hσ j ![1] 0).add
        ((hu.clm_comp (coordMap 1 1)).coeffSmul hc hν tr hbuc hσ j ![1] 1)))
  refine hasHInfDerivOn_congr hd_sum
    (fun {s} hs => (bvOp_dtIterV_eq_sum tr hσ j (u s) hs).symm)
    (fun {s} hs => ?_)
  rw [bvOp_dtIterV_eq_sum tr hσ (j + 1) (u s) hs, bvOp_dtIterV_eq_sum tr hσ j (u' s) hs]
  funext y
  simp only [Pi.add_apply]
  abel

/-! ## 4. Base Step: `HasHInfDerivOn c w w₁` from the Weak Oseen Identity -/

/-- `IsRealSpatialSmoothOseenSlices c w W Wq Wη` immediately gives `IsHInfContOn c w`. -/
lemma isHInfContOn_of_spatialSmoothSlices {c : ℝ}
    {w W Wq Wη : ℝ → B0579.Plane → F8Ex.RMerid}
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη) :
    IsHInfContOn c w where
  hinf {s} hs :=
    { smooth := hsp.spatial_smooth s hs
      periodic := hsp.periodic s hs
      memL2 := hsp.memL2_all s hs }
  cont {n} α := by
    rw [isOpen_Ioo.continuousOn_iff]
    intro s hs
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have htend_enn := hsp.cont_all s hs n α
    have htend_real : Tendsto
        (fun t => (F8Ex.cellL2R c (fun y => F8Ex.slicePdIterR α (w t) y -
          F8Ex.slicePdIterR α (w s) y)).toReal) (𝓝 s) (𝓝 0) := by
      have hcomp := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend_enn
      rw [show (0 : ℝ≥0∞).toReal = 0 by simp] at hcomp
      exact hcomp
    refine htend_real.congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    have h1 := uL2_eq_toLpCell α (hsp.memL2_all t ht n α)
    have h2 := uL2_eq_toLpCell α (hsp.memL2_all s hs n α)
    have hsub : uL2 c α w t - uL2 c α w s =
        toLpCell ((hsp.memL2_all t ht n α).sub (hsp.memL2_all s hs n α)) := by
      rw [h1, h2, ← toLpCell_sub]
    have henn : F8Ex.cellL2R c (fun y => F8Ex.slicePdIterR α (w t) y -
        F8Ex.slicePdIterR α (w s) y) = ENNReal.ofReal ‖uL2 c α w t - uL2 c α w s‖ := by
      rw [hsub, ofReal_norm_toLpCell]
      rfl
    rw [henn, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Direct Banach-space FTC on `(0, 2)` without second-countability assumptions: if `f` is
continuous on `(0, 2)` and `u t - u a = ∫ r in a..t, f r` for all `a, t ∈ (0, 2)`, then
`HasDerivAt u (f s) s` holds at every `s ∈ (0, 2)`. -/
private lemma hasDerivAt_of_sub_eq_intervalIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u f : ℝ → E} (hf : ContinuousOn f (Ioo (0 : ℝ) 2))
    (hsub : ∀ {a t : ℝ}, a ∈ Ioo (0 : ℝ) 2 → t ∈ Ioo (0 : ℝ) 2 → u t - u a = ∫ r in a..t, f r)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    HasDerivAt u (f s) s := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont_at : ContinuousAt f s := hf.continuousAt (isOpen_Ioo.mem_nhds hs)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.continuousAt_iff.mp hcont_at ε hε
  let δ := min δ₁ (min (s / 2) ((2 - s) / 2))
  have hδ : 0 < δ := lt_min hδ₁ (lt_min (by linarith [hs.1]) (by linarith [hs.2]))
  have hev : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    have hc_abs : ContinuousAt (fun h : ℝ => |h|) 0 := continuous_abs.continuousAt
    have ht_abs : Tendsto (fun h : ℝ => |h|) (𝓝 0) (𝓝 0) := by
      simpa using hc_abs.tendsto
    exact ht_abs.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with h hh
  have hs_le1 : δ ≤ s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs_le2 : δ ≤ (2 - s) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hh_δ₁ : |h| < δ₁ := lt_of_lt_of_le hh (min_le_left _ _)
  have hsh : s + h ∈ Ioo (0 : ℝ) 2 := by
    obtain ⟨hl, hu⟩ := abs_lt.mp hh
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have huIcc : uIcc s (s + h) ⊆ Ioo (0 : ℝ) 2 := fun r hr =>
    ⟨lt_of_lt_of_le (lt_min hs.1 hsh.1) hr.1, lt_of_le_of_lt hr.2 (max_lt hs.2 hsh.2)⟩
  have hint_f : IntervalIntegrable f volume s (s + h) :=
    (hf.mono huIcc).intervalIntegrable
  have hint_c : IntervalIntegrable (fun _ : ℝ => f s) volume s (s + h) :=
    intervalIntegrable_const
  have hrem : u (s + h) - u s - h • f s = ∫ r in s..(s + h), (f r - f s) := by
    have hh_eq : s + h - s = h := add_sub_cancel_left s h
    rw [hsub hs hsh, ← hh_eq, ← intervalIntegral.integral_const (a := s) (b := s + h) (f s),
      hh_eq, ← intervalIntegral.integral_sub hint_f hint_c]
  rw [hrem]
  have hb_on : ∀ r ∈ uIoc s (s + h), ‖f r - f s‖ ≤ ε := by
    intro r hr
    have hr_uIcc : r ∈ uIcc s (s + h) := uIoc_subset_uIcc hr
    have hr_dist : dist r s < δ₁ := by
      rw [Real.dist_eq]
      have h1 : |r - s| ≤ |s + h - s| := abs_sub_left_of_mem_uIcc hr_uIcc
      rw [add_sub_cancel_left] at h1
      exact lt_of_le_of_lt h1 hh_δ₁
    rw [← dist_eq_norm]
    exact (hball hr_dist).le
  calc ‖∫ r in s..(s + h), (f r - f s)‖
      ≤ ε * |s + h - s| := intervalIntegral.norm_integral_le_of_norm_le_const hb_on
    _ = ε * ‖h‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]

private lemma mem_divFree_of_smooth_div_zero {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f)
    (hdiv : ∀ y : B0579.Plane, F8Ex.slicePdR 0 f y 0 + F8Ex.slicePdR 1 f y 1 = 0) :
    toLpCell (hf.memL2 0 Fin.elim0) ∈ Cyl.divFree c := by
  rw [toLpCell_mem_divFree_iff]
  intro ψ hψ
  have hψ' : Sob.IsCylTest c ψ := isCylTest_iff_b0579.mpr hψ
  have hdψ := hψ'.differentiable
  have h0_sm : ContDiff ℝ ∞ (fun y => f y 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hf.smooth
  have h1_sm : ContDiff ℝ ∞ (fun y => f y 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hf.smooth
  have h0_per : Cyl.IsPeriodic c (fun y => f y 0) :=
    fun z => congrArg (fun v : Cyl.Vec2 => v 0) (hf.periodic z)
  have hpQ_eq : Cyl.partialQ (fun y => f y 0) = fun y => F8Ex.slicePdR 0 f y 0 := by
    funext y
    rw [Cyl.partialQ_eq_fderiv (h0_sm.differentiable (by simp)) y,
      PartI.csb_fderiv_comp_apply ((hf.smooth.differentiable (by simp)) y) 0]
    rfl
  have hpE_eq : Cyl.partialEta (fun y => f y 1) = fun y => F8Ex.slicePdR 1 f y 1 := by
    funext y
    rw [Cyl.partialEta_eq_fderiv (h1_sm.differentiable (by simp)) y,
      PartI.csb_fderiv_comp_apply ((hf.smooth.differentiable (by simp)) y) 1]
    rfl
  have hm_f0 : MemLp (fun y => f y 0) 2 (Cyl.cellμ c) :=
    (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
      (memLp_to_cellμ (hf.memL2 0 Fin.elim0))
  have hm_f1 : MemLp (fun y => f y 1) 2 (Cyl.cellμ c) :=
    (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
      (memLp_to_cellμ (hf.memL2 0 Fin.elim0))
  have hm_df0 : MemLp (Cyl.partialQ (fun y => f y 0)) 2 (Cyl.cellμ c) := by
    rw [hpQ_eq]
    exact (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
      (memLp_to_cellμ (hf.memL2 1 ![0]))
  have hm_df1 : MemLp (Cyl.partialEta (fun y => f y 1)) 2 (Cyl.cellμ c) := by
    rw [hpE_eq]
    exact (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
      (memLp_to_cellμ (hf.memL2 1 ![1]))
  have hi_q1 : IntegrableOn (fun y => Cyl.partialQ ψ y * f y 0) (Cyl.cell c) :=
    Cyl.integrableOn_test_mul (Cyl.isCylTest_partialQ hψ') hm_f0
  have hi_q2 : IntegrableOn (fun y => ψ y * Cyl.partialQ (fun z => f z 0) y) (Cyl.cell c) :=
    Cyl.integrableOn_test_mul hψ' hm_df0
  have hi_e0 : IntegrableOn (fun y => ψ y * f y 1) (Cyl.cell c) :=
    Cyl.integrableOn_test_mul hψ' hm_f1
  have hi_e1 : IntegrableOn (fun y => Cyl.partialEta ψ y * f y 1) (Cyl.cell c) :=
    Cyl.integrableOn_test_mul (Cyl.isCylTest_partialEta hψ') hm_f1
  have hi_e2 : IntegrableOn (fun y => ψ y * Cyl.partialEta (fun z => f z 1) y) (Cyl.cell c) :=
    Cyl.integrableOn_test_mul hψ' hm_df1
  have hψ_per : Cyl.IsPeriodic c ψ := fun z => hψ.periodic z
  have hibp_q := Cyl.integral_cell_partialQ_mul hc hdψ (h0_sm.differentiable (by simp))
    hψ_per h0_per hi_q1 hi_q2
  have hibp_e := Cyl.integral_cell_partialEta_mul hdψ (h1_sm.differentiable (by simp))
    hi_e0 hi_e1 hi_e2
  have hpt_lhs : ∀ y : B0579.Plane,
      f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y =
        Cyl.partialQ ψ y * f y 0 + Cyl.partialEta ψ y * f y 1 := by
    intro y
    rw [Cyl.partialQ_eq_fderiv hdψ y, Cyl.partialEta_eq_fderiv hdψ y]
    change f y 0 * fderiv ℝ ψ y (1, 0) + f y 1 * fderiv ℝ ψ y (0, 1) = _
    ring
  have hint_tot : IntegrableOn
      (fun y => f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y) (B0579.cell c) := by
    rw [b0579_cell_eq_cyl_cell]
    exact (hi_q1.add hi_e1).congr_fun (fun y _ => (hpt_lhs y).symm) (Cyl.measurableSet_cell c)
  refine ⟨hint_tot, ?_⟩
  change (∫ y in B0579.cell c, (f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y)) = 0
  rw [b0579_cell_eq_cyl_cell,
    setIntegral_congr_fun (Cyl.measurableSet_cell c) (fun y _ => hpt_lhs y),
    integral_add hi_q1 hi_e1, hibp_q, hibp_e, ← neg_add, ← integral_add hi_q2 hi_e2]
  have hzero : ∀ y : B0579.Plane,
      ψ y * Cyl.partialQ (fun z => f z 0) y + ψ y * Cyl.partialEta (fun z => f z 1) y = 0 := by
    intro y
    rw [hpQ_eq, hpE_eq, ← mul_add, hdiv y, mul_zero]
  simp [hzero]

private lemma toLpCell_realSolCylTest_mem_divFree {c : ℝ} (hc : 0 < c)
    {Φ : B0579.Plane → F8Ex.RMerid} (hΦ : F8Ex.IsRealSolCylTest c Φ) :
    toLpCell (F8Ex.memLp_realSolCylTest hΦ) ∈ Cyl.divFree c := by
  have hΦ_sm : ContDiff ℝ ∞ Φ := by
    have h0 := (hΦ.cyl_test 0).smooth
    have h1 := (hΦ.cyl_test 1).smooth
    have heq : Φ = fun y => ((ContinuousLinearMap.id ℝ ℝ).smulRight F8Ex.eR0) (Φ y 0) +
        ((ContinuousLinearMap.id ℝ ℝ).smulRight F8Ex.eR1) (Φ y 1) := by
      funext y; ext k; fin_cases k <;> simp [F8Ex.eR0, F8Ex.eR1]
    rw [heq]
    exact ((((ContinuousLinearMap.id ℝ ℝ).smulRight F8Ex.eR0).contDiff.comp h0).add
      (((ContinuousLinearMap.id ℝ ℝ).smulRight F8Ex.eR1).contDiff.comp h1))
  have hΦ_per : Cyl.IsPeriodic c Φ := fun y => by
    ext k; exact (hΦ.cyl_test k).periodic y
  have hΦ_hinf : IsCylSmoothHInf c Φ :=
    { smooth := hΦ_sm
      periodic := hΦ_per
      memL2 := fun n α => by
        obtain ⟨R0, hR0⟩ := (isCylTest_iff_b0579.mpr (hΦ.cyl_test 0)).bounded
        obtain ⟨R1, hR1⟩ := (isCylTest_iff_b0579.mpr (hΦ.cyl_test 1)).bounded
        have hvan : ∀ y : B0579.Plane, max R0 R1 < |y.2| → F8Ex.slicePdIterR α Φ y = 0 := by
          have hΦ_van : ∀ y : B0579.Plane, max R0 R1 < |y.2| → Φ y = 0 := by
            intro y hy
            ext k
            fin_cases k
            · exact hR0 y (lt_of_le_of_lt (le_max_left _ _) hy)
            · exact hR1 y (lt_of_le_of_lt (le_max_right _ _) hy)
          intro y hy
          have hop : IsOpen {z : B0579.Plane | max R0 R1 < |z.2|} :=
            isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
          have heq_on : EqOn Φ 0 {z : B0579.Plane | max R0 R1 < |z.2|} :=
            fun z hz => hΦ_van z hz
          have hiter := Sob.iterD_eqOn hop heq_on (List.ofFn fun i => (Sob.cylinder c).dir (α i)) hy
          rw [iterD_ofFn_eq_slicePdIterR, iterD_ofFn_eq_slicePdIterR, slicePdIterR_zero] at hiter
          exact hiter
        exact memLp_of_cellμ (Cyl.memLp_of_vanishes (contDiff_slicePdIterR hΦ_sm α).continuous
          (fun y hy => hvan y hy) 2) }
  have hdiv : ∀ y : B0579.Plane, F8Ex.slicePdR 0 Φ y 0 + F8Ex.slicePdR 1 Φ y 1 = 0 := by
    intro y
    have hd := (hΦ_sm.differentiable (by simp)) y
    have h0 : Cyl.partialQ (fun z => Φ z 0) y = F8Ex.slicePdR 0 Φ y 0 := by
      rw [Cyl.partialQ_eq_fderiv ((hΦ.cyl_test 0).differentiable) y,
        PartI.csb_fderiv_comp_apply hd 0]
      rfl
    have h1 : Cyl.partialEta (fun z => Φ z 1) y = F8Ex.slicePdR 1 Φ y 1 := by
      rw [Cyl.partialEta_eq_fderiv ((hΦ.cyl_test 1).differentiable) y,
        PartI.csb_fderiv_comp_apply hd 1]
      rfl
    have hdf := hΦ.div_free y
    unfold Cyl.divergence at hdf
    linarith
  have hm := mem_divFree_of_smooth_div_zero hc hΦ_hinf hdiv
  have heq : toLpCell (F8Ex.memLp_realSolCylTest hΦ) = toLpCell (hΦ_hinf.memL2 0 Fin.elim0) :=
    toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  rwa [heq]

private lemma div_zero_slicePdIterR {f : B0579.Plane → F8Ex.RMerid} (hf : ContDiff ℝ ∞ f)
    (hdiv : ∀ y : B0579.Plane, F8Ex.slicePdR 0 f y 0 + F8Ex.slicePdR 1 f y 1 = 0) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) (y : B0579.Plane),
      F8Ex.slicePdR 0 (F8Ex.slicePdIterR α f) y 0 +
        F8Ex.slicePdR 1 (F8Ex.slicePdIterR α f) y 1 = 0
  | 0, _, y => hdiv y
  | _ + 1, α, y => by
      have ih : ∀ z, F8Ex.slicePdR 0 (F8Ex.slicePdIterR (Fin.tail α) f) z 0 +
          F8Ex.slicePdR 1 (F8Ex.slicePdIterR (Fin.tail α) f) z 1 = 0 :=
        div_zero_slicePdIterR hf hdiv (Fin.tail α)
      let g := F8Ex.slicePdIterR (Fin.tail α) f
      have hg : ContDiff ℝ ∞ g := contDiff_slicePdIterR hf (Fin.tail α)
      have hsymm : ∀ (d : Fin 2),
          F8Ex.slicePdR d (F8Ex.slicePdR (α 0) g) y =
            F8Ex.slicePdR (α 0) (F8Ex.slicePdR d g) y := by
        intro d
        have hsm2 : ContDiff ℝ (2 : WithTop ℕ∞) g := hg.of_le (by simp)
        have hd2 : DifferentiableAt ℝ (fderiv ℝ g) y :=
          ((hsm2.contDiffAt (x := y)).fderiv_right (by norm_num)).differentiableAt one_ne_zero
        have hl : fderiv ℝ (fun z => fderiv ℝ g z (B0579.dir (α 0))) y (B0579.dir d) =
            fderiv ℝ (fderiv ℝ g) y (B0579.dir d) (B0579.dir (α 0)) := by
          have hc := (ContinuousLinearMap.apply ℝ F8Ex.RMerid (B0579.dir (α 0))).hasFDerivAt.comp
            y hd2.hasFDerivAt
          exact congrArg (fun L => L (B0579.dir d)) hc.fderiv
        have hr : fderiv ℝ (fun z => fderiv ℝ g z (B0579.dir d)) y (B0579.dir (α 0)) =
            fderiv ℝ (fderiv ℝ g) y (B0579.dir (α 0)) (B0579.dir d) := by
          have hc := (ContinuousLinearMap.apply ℝ F8Ex.RMerid (B0579.dir d)).hasFDerivAt.comp
            y hd2.hasFDerivAt
          exact congrArg (fun L => L (B0579.dir (α 0))) hc.fderiv
        change fderiv ℝ (fun z => fderiv ℝ g z (B0579.dir (α 0))) y (B0579.dir d) =
          fderiv ℝ (fun z => fderiv ℝ g z (B0579.dir d)) y (B0579.dir (α 0))
        rw [hl, hr]
        exact (ContDiffAt.isSymmSndFDerivAt (n := 2) (hsm2.contDiffAt (x := y)) (by simp)).eq
          (B0579.dir d) (B0579.dir (α 0))
      simp only [F8Ex.slicePdIterR]
      change F8Ex.slicePdR 0 (F8Ex.slicePdR (α 0) g) y 0 +
        F8Ex.slicePdR 1 (F8Ex.slicePdR (α 0) g) y 1 = 0
      rw [hsymm 0, hsymm 1]
      have hd0 : DifferentiableAt ℝ (F8Ex.slicePdR 0 g) y :=
        ((contDiff_slicePdR hg 0).differentiable (by simp)) y
      have hd1 : DifferentiableAt ℝ (F8Ex.slicePdR 1 g) y :=
        ((contDiff_slicePdR hg 1).differentiable (by simp)) y
      change (fderiv ℝ (F8Ex.slicePdR 0 g) y (B0579.dir (α 0))) 0 +
        (fderiv ℝ (F8Ex.slicePdR 1 g) y (B0579.dir (α 0))) 1 = 0
      rw [← PartI.csb_fderiv_comp_apply hd0 0 (B0579.dir (α 0)),
        ← PartI.csb_fderiv_comp_apply hd1 1 (B0579.dir (α 0))]
      have hsum_fn : (fun z => F8Ex.slicePdR 0 g z 0 + F8Ex.slicePdR 1 g z 1) = fun _ => 0 :=
        funext ih
      have hd0_proj : DifferentiableAt ℝ (fun z => F8Ex.slicePdR 0 g z 0) y :=
        (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).differentiableAt.comp y hd0
      have hd1_proj : DifferentiableAt ℝ (fun z => F8Ex.slicePdR 1 g z 1) y :=
        (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).differentiableAt.comp y hd1
      have hdf_add := fderiv_fun_add hd0_proj hd1_proj
      have h0 : fderiv ℝ (fun z => F8Ex.slicePdR 0 g z 0 + F8Ex.slicePdR 1 g z 1) y
          (B0579.dir (α 0)) = 0 := by
        rw [hsum_fn]
        simp
      rw [hdf_add, add_apply] at h0
      exact h0

/-- Propagation of the integral identity `u t - u a = ∫ r in a..t, u' r` from `α = Fin.elim0` to
all spatial multi-indices `α : Fin n → Fin 2` via cylinder test integration by parts in `Cyl.L2v c`. -/
private lemma sub_eq_intervalIntegral_slicePdR {c : ℝ} (hc : 0 < c)
    {g g' : ℝ → B0579.Plane → F8Ex.RMerid}
    (hg : IsHInfContOn c g) (hg' : IsHInfContOn c g')
    (h0 : ∀ {a t : ℝ}, a ∈ Ioo (0 : ℝ) 2 → t ∈ Ioo (0 : ℝ) 2 →
      uL2 c Fin.elim0 g t - uL2 c Fin.elim0 g a = ∫ r in a..t, uL2 c Fin.elim0 g' r)
    (d : Fin 2) {a t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 2) (ht : t ∈ Ioo (0 : ℝ) 2) :
    uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g s)) t -
      uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g s)) a =
        ∫ r in a..t, uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g' s)) r := by
  let testVec (i : Fin 2) (ψ : B0579.Plane → ℝ) : B0579.Plane → F8Ex.RMerid :=
    fun y => ψ y • eVec i
  have hm_testVec : ∀ (i : Fin 2) {ψ : B0579.Plane → ℝ} (hψ : Sob.IsCylTest c ψ),
      MemLp (testVec i ψ) 2 (F8Ex.cellMeas c) := by
    intro i ψ hψ
    obtain ⟨R, hR⟩ := hψ.bounded
    exact memLp_of_cellμ (Cyl.memLp_of_vanishes (hψ.smooth.continuous.smul continuous_const)
      (fun y hy => by dsimp [testVec]; rw [hR y hy, zero_smul]) 2)
  have hibp_vec : ∀ (i : Fin 2) {ψ : B0579.Plane → ℝ} (hψ : Sob.IsCylTest c ψ)
      {h : B0579.Plane → F8Ex.RMerid} (hh : IsCylSmoothHInf c h),
      ⟪toLpCell (hm_testVec i hψ), toLpCell ((hh.slicePdR d).memL2 0 Fin.elim0)⟫_ℝ =
        -⟪toLpCell (hm_testVec i (hψ.dirDeriv (B0579.dir d))),
            toLpCell (hh.memL2 0 Fin.elim0)⟫_ℝ := by
    intro i ψ hψ h hh
    rw [inner_toLpCell_eq, inner_toLpCell_eq, b0579_cell_eq_cyl_cell]
    have hpt1 : ∀ y : B0579.Plane,
        ⟪testVec i ψ y, F8Ex.slicePdR d h y⟫_ℝ =
          fderiv ℝ (fun z => ψ z • h z i) y (B0579.dir d) -
            fderiv ℝ ψ y (B0579.dir d) * h y i := by
      intro y
      have hd_ψ : DifferentiableAt ℝ ψ y := (hψ.smooth.differentiable (by simp)) y
      have hd_h : DifferentiableAt ℝ h y := (hh.smooth.differentiable (by simp)) y
      have hd_hi : DifferentiableAt ℝ (fun z => h z i) y :=
        (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).differentiableAt.comp y hd_h
      have hsm : fderiv ℝ (fun z : B0579.Plane => ψ z • h z i) y (B0579.dir d) =
          fderiv ℝ ψ y (B0579.dir d) * h y i + ψ y * fderiv ℝ (fun z => h z i) y (B0579.dir d) := by
        change fderiv ℝ (ψ • fun z => h z i) y (B0579.dir d) = _
        rw [fderiv_smul hd_ψ hd_hi]
        simp only [add_apply, smul_apply,
          ContinuousLinearMap.smulRight_apply, smul_eq_mul]
        ring
      rw [PartI.csb_fderiv_comp_apply hd_h i (B0579.dir d)] at hsm
      change fderiv ℝ (fun z : B0579.Plane => ψ z • h z i) y (B0579.dir d) =
        fderiv ℝ ψ y (B0579.dir d) * h y i + ψ y * F8Ex.slicePdR d h y i at hsm
      have hinn : ⟪testVec i ψ y, F8Ex.slicePdR d h y⟫_ℝ = ψ y * F8Ex.slicePdR d h y i :=
        inner_smul_eVec i (ψ y) (F8Ex.slicePdR d h y)
      linarith
    have hpt2 : ∀ y : B0579.Plane,
        ⟪testVec i (fun z => fderiv ℝ ψ z (B0579.dir d)) y, h y⟫_ℝ =
          fderiv ℝ ψ y (B0579.dir d) * h y i :=
      fun y => inner_smul_eVec i (fderiv ℝ ψ y (B0579.dir d)) (h y)
    have hprod_sm : Sob.IsCylSmooth c (fun z : B0579.Plane => ψ z • h z i) := by
      refine ⟨hψ.smooth.smul ((EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hh.smooth),
        fun z => ?_, ?_⟩
      · have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
        rw [hψ.periodic z, hz, congrArg (fun v : Cyl.Vec2 => v i) (hh.periodic z)]
      · obtain ⟨R, hR⟩ := hψ.bounded
        exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩
    have h0_int : ∫ y in Cyl.cell c, fderiv ℝ (fun z => ψ z • h z i) y (B0579.dir d) = 0 := by
      rw [Sob.cyl_cell_eq]
      exact Sob.integral_cylCell_fderiv_eq_zero hc hprod_sm (B0579.dir d)
    have hi1 : IntegrableOn (fun y => fderiv ℝ (fun z => ψ z • h z i) y (B0579.dir d))
        (Cyl.cell c) := by
      rw [Sob.cyl_cell_eq]
      exact (hprod_sm.dir (B0579.dir d)).integrableOn
    have hi2 : IntegrableOn (fun y => fderiv ℝ ψ y (B0579.dir d) * h y i) (Cyl.cell c) :=
      Cyl.integrableOn_test_mul (hψ.dirDeriv (B0579.dir d))
        ((EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
          (memLp_to_cellμ (hh.memL2 0 Fin.elim0)))
    change (∫ y in Cyl.cell c, ⟪testVec i ψ y, F8Ex.slicePdR d h y⟫_ℝ) =
      -(∫ y in Cyl.cell c, ⟪testVec i (fun z => fderiv ℝ ψ z (B0579.dir d)) y, h y⟫_ℝ)
    simp_rw [hpt1, hpt2]
    rw [integral_sub hi1 hi2, h0_int, zero_sub]
  set Δ : Cyl.L2v c :=
    (uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g s)) t -
      uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g s)) a) -
      ∫ r in a..t, uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g' s)) r
  suffices hΔ : Δ = 0 from sub_eq_zero.mp hΔ
  have huIcc : uIcc a t ⊆ Ioo (0 : ℝ) 2 := fun r hr =>
    ⟨lt_of_lt_of_le (lt_min ha.1 ht.1) hr.1, lt_of_le_of_lt hr.2 (max_lt ha.2 ht.2)⟩
  have hint_g' : IntervalIntegrable (uL2 c Fin.elim0 g') volume a t :=
    ((hg'.cont Fin.elim0).mono huIcc).intervalIntegrable
  have hint_dg' : IntervalIntegrable
      (uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g' s))) volume a t :=
    (((hg'.slicePdR d).cont Fin.elim0).mono huIcc).intervalIntegrable
  have horth_Δ : ∀ (i : Fin 2) {ψ : B0579.Plane → ℝ} (hψ : Sob.IsCylTest c ψ),
      ⟪toLpCell (hm_testVec i hψ), Δ⟫_ℝ = 0 := by
    intro i ψ hψ
    let L1 : Cyl.L2v c →L[ℝ] ℝ := innerSL ℝ (toLpCell (hm_testVec i hψ))
    let L2 : Cyl.L2v c →L[ℝ] ℝ := innerSL ℝ (toLpCell (hm_testVec i (hψ.dirDeriv (B0579.dir d))))
    change L1 Δ = 0
    simp only [Δ, map_sub]
    rw [← L1.intervalIntegral_comp_comm hint_dg']
    have hint_eq : (∫ r in a..t, L1 (uL2 c Fin.elim0 (fun s => F8Ex.slicePdR d (g' s)) r)) =
        -(∫ r in a..t, L2 (uL2 c Fin.elim0 g' r)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun r hr => ?_
      have hr' := huIcc hr
      rw [(hg'.slicePdR d).uL2_eq Fin.elim0 hr', hg'.uL2_eq Fin.elim0 hr']
      exact hibp_vec i hψ (hg'.hinf hr')
    rw [hint_eq, L2.intervalIntegral_comp_comm hint_g', ← h0 ha ht, map_sub,
      (hg.slicePdR d).uL2_eq Fin.elim0 ht, (hg.slicePdR d).uL2_eq Fin.elim0 ha,
      hg.uL2_eq Fin.elim0 ht, hg.uL2_eq Fin.elim0 ha]
    have h_t := hibp_vec i hψ (hg.hinf ht)
    have h_a := hibp_vec i hψ (hg.hinf ha)
    change ⟪toLpCell (hm_testVec i hψ), toLpCell (((hg.hinf ht).slicePdR d).memL2 0 Fin.elim0)⟫_ℝ -
        ⟪toLpCell (hm_testVec i hψ), toLpCell (((hg.hinf ha).slicePdR d).memL2 0 Fin.elim0)⟫_ℝ -
        -(⟪toLpCell (hm_testVec i (hψ.dirDeriv (B0579.dir d))),
            toLpCell ((hg.hinf ht).memL2 0 Fin.elim0)⟫_ℝ -
          ⟪toLpCell (hm_testVec i (hψ.dirDeriv (B0579.dir d))),
            toLpCell ((hg.hinf ha).memL2 0 Fin.elim0)⟫_ℝ) = 0
    linarith
  have hae_comp : ∀ i : Fin 2,
      (fun y => (Δ : B0579.Plane → Cyl.Vec2) y i) =ᵐ[Cyl.cellμ c] 0 := by
    intro i
    let Δi : B0579.Plane → ℝ := fun y => (Δ : B0579.Plane → Cyl.Vec2) y i
    have hm_Δi : MemLp Δi 2 (Sob.cylinder c).μ :=
      (Cyl.cylinder_μ_eq c).symm ▸
        ((EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp Δ))
    have hae_cyl : Δi =ᵐ[(Sob.cylinder c).μ] 0 := by
      refine (Sob.cylinder c).ae_zero Δi (hm_Δi.locallyIntegrable (by norm_num)) (fun ψ hψ => ?_)
      have h0_ψ := horth_Δ i hψ
      rw [inner_toLpCell_left] at h0_ψ
      rw [Cyl.cylinder_μ_eq c]
      unfold Cyl.cellμ
      rw [← h0_ψ]
      refine setIntegral_congr_fun (Cyl.measurableSet_cell c) fun y _ => ?_
      exact (inner_smul_eVec i (ψ y) ((Δ : B0579.Plane → Cyl.Vec2) y)).symm
    rwa [Cyl.cylinder_μ_eq c] at hae_cyl
  apply Lp.ext
  filter_upwards [hae_comp 0, hae_comp 1, Lp.coeFn_zero Cyl.Vec2 2 (Cyl.cellμ c)] with y hy0 hy1 hyZ
  rw [hyZ]
  ext i
  fin_cases i
  · exact hy0
  · exact hy1

private lemma sub_eq_intervalIntegral_all {c : ℝ} (hc : 0 < c) :
    ∀ (n : ℕ) {g g' : ℝ → B0579.Plane → F8Ex.RMerid},
      IsHInfContOn c g → IsHInfContOn c g' →
      (∀ {a t : ℝ}, a ∈ Ioo (0 : ℝ) 2 → t ∈ Ioo (0 : ℝ) 2 →
        uL2 c Fin.elim0 g t - uL2 c Fin.elim0 g a = ∫ r in a..t, uL2 c Fin.elim0 g' r) →
      ∀ (α : Fin n → Fin 2) {a t : ℝ}, a ∈ Ioo (0 : ℝ) 2 → t ∈ Ioo (0 : ℝ) 2 →
        uL2 c α g t - uL2 c α g a = ∫ r in a..t, uL2 c α g' r
  | 0, g, g', _, _, h0, α, a, t, ha, ht => by
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      exact h0 ha ht
  | n + 1, g, g', hg, hg', h0, α, a, t, ha, ht => by
      obtain ⟨β, d, rfl⟩ := exists_snocIdx α
      have ih := sub_eq_intervalIntegral_all hc n (hg.slicePdR d) (hg'.slicePdR d)
        (fun {a' t'} ha' ht' => sub_eq_intervalIntegral_slicePdR hc hg hg' h0 d ha' ht') β ha ht
      have hfun_g : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
          uL2 c β (fun r => F8Ex.slicePdR d (g r)) s = uL2 c (snocIdx β d) g s := by
        intro s hs
        rw [(hg.slicePdR d).uL2_eq β hs, hg.uL2_eq (snocIdx β d) hs]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun _ => by rw [slicePdIterR_slicePdR])
      have hfun_g' : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
          uL2 c β (fun r => F8Ex.slicePdR d (g' r)) s = uL2 c (snocIdx β d) g' s := by
        intro s hs
        rw [(hg'.slicePdR d).uL2_eq β hs, hg'.uL2_eq (snocIdx β d) hs]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun _ => by rw [slicePdIterR_slicePdR])
      have huIcc : uIcc a t ⊆ Ioo (0 : ℝ) 2 := fun r hr =>
        ⟨lt_of_lt_of_le (lt_min ha.1 ht.1) hr.1, lt_of_le_of_lt hr.2 (max_lt ha.2 ht.2)⟩
      rw [hfun_g ht, hfun_g ha] at ih
      exact ih.trans (intervalIntegral.integral_congr fun r hr => hfun_g' (huIcc hr))

@[simp]
lemma dtIterV_zero (V : ℝ → B0579.Plane → F8Ex.RMerid) : dtIterV 0 V = V := by
  funext s y
  simp [dtIterV]

/-- **Base step**: `w` has `H^∞(C_c)` time derivative
`w₁ s := ν • sliceLapR (w s) - P0Smooth c (bvOp (V s) (w s))` on `(0, 2)`. -/
theorem hasHInfDerivOn_w {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη) :
    HasHInfDerivOn c w
      (fun s => ν • sliceLapR (w s) -
        P0Smooth c (bvOp (F8Ex.shiftedDriftTrain tr σ s) (w s))) := by
  let V := F8Ex.shiftedDriftTrain tr σ
  let w1 : ℝ → B0579.Plane → F8Ex.RMerid :=
    fun s => ν • sliceLapR (w s) - P0Smooth c (bvOp (V s) (w s))
  have hw_cont : IsHInfContOn c w := isHInfContOn_of_spatialSmoothSlices hsp
  have hbv_cont : IsHInfContOn c (fun s => bvOp (V s) (w s)) := by
    simpa only [dtIterV_zero] using hw_cont.bvOp_dtIterV hc hν tr hbuc hσ 0
  have hw1_cont : IsHInfContOn c w1 :=
    (hw_cont.sliceLapR.smul ν).sub (hbv_cont.P0Smooth hc)
  have h0_int : ∀ {a t : ℝ}, a ∈ Ioo (0 : ℝ) 2 → t ∈ Ioo (0 : ℝ) 2 →
      uL2 c Fin.elim0 w t - uL2 c Fin.elim0 w a = ∫ r in a..t, uL2 c Fin.elim0 w1 r := by
    intro a t ha ht
    set Δ : Cyl.L2v c :=
      (uL2 c Fin.elim0 w t - uL2 c Fin.elim0 w a) - ∫ r in a..t, uL2 c Fin.elim0 w1 r
    suffices hΔ : Δ = 0 from sub_eq_zero.mp hΔ
    have huIcc : uIcc a t ⊆ Ioo (0 : ℝ) 2 := fun r hr =>
      ⟨lt_of_lt_of_le (lt_min ha.1 ht.1) hr.1, lt_of_le_of_lt hr.2 (max_lt ha.2 ht.2)⟩
    have hint_w1 : IntervalIntegrable (uL2 c Fin.elim0 w1) volume a t :=
      ((hw1_cont.cont Fin.elim0).mono huIcc).intervalIntegrable
    -- Show `Δ ∈ Cyl.divFree c`
    have hw_divFree : ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 2 → uL2 c Fin.elim0 w r ∈ Cyl.divFree c := by
      intro r hr
      rw [hw_cont.uL2_eq Fin.elim0 hr]
      exact mem_divFree_of_smooth_div_zero hc (hw_cont.hinf hr) (hsp.div_free r hr)
    have hw1_divFree : ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 2 → uL2 c Fin.elim0 w1 r ∈ Cyl.divFree c := by
      intro r hr
      have hlap_div : ∀ y : B0579.Plane,
          F8Ex.slicePdR 0 (sliceLapR (w r)) y 0 +
            F8Ex.slicePdR 1 (sliceLapR (w r)) y 1 = 0 := by
        intro y
        have hsm00 := contDiff_slicePdIterR (hw_cont.hinf hr).smooth ![0, 0]
        have hsm11 := contDiff_slicePdIterR (hw_cont.hinf hr).smooth ![1, 1]
        unfold sliceLapR
        have h00 : F8Ex.slicePdR 0 (F8Ex.slicePdR 0 (w r)) = F8Ex.slicePdIterR ![0, 0] (w r) := rfl
        have h11 : F8Ex.slicePdR 1 (F8Ex.slicePdR 1 (w r)) = F8Ex.slicePdIterR ![1, 1] (w r) := rfl
        rw [h00, h11, slicePdR_add hsm00 hsm11 0, slicePdR_add hsm00 hsm11 1]
        simp only [Pi.add_apply, PiLp.add_apply]
        have hd0 := div_zero_slicePdIterR (hw_cont.hinf hr).smooth (hsp.div_free r hr) ![0, 0] y
        have hd1 := div_zero_slicePdIterR (hw_cont.hinf hr).smooth (hsp.div_free r hr) ![1, 1] y
        linarith
      have hlap_mem : toLpCell ((hw_cont.hinf hr).sliceLapR.memL2 0 Fin.elim0) ∈ Cyl.divFree c :=
        mem_divFree_of_smooth_div_zero hc (hw_cont.hinf hr).sliceLapR hlap_div
      have hp0_mem : toLpCell
          ((P0Smooth_isCylSmoothHInf hc (hbv_cont.hinf hr)).memL2 0 Fin.elim0) ∈ Cyl.divFree c := by
        rw [toLpCell_P0Smooth hc (hbv_cont.hinf hr)]
        exact Cyl.P0_mem _
      have hw1_eq : uL2 c Fin.elim0 w1 r =
          ν • toLpCell ((hw_cont.hinf hr).sliceLapR.memL2 0 Fin.elim0) -
            toLpCell ((P0Smooth_isCylSmoothHInf hc (hbv_cont.hinf hr)).memL2 0 Fin.elim0) := by
        rw [hw1_cont.uL2_eq Fin.elim0 hr, ← toLpCell_smul, ← toLpCell_sub]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
      rw [hw1_eq]
      exact (Cyl.divFree c).sub_mem ((Cyl.divFree c).smul_mem ν hlap_mem) hp0_mem
    have hint_mem_divFree : (∫ r in a..t, uL2 c Fin.elim0 w1 r) ∈ Cyl.divFree c := by
      rw [Cyl.mem_divFree]
      intro ψ hψ
      let Lψ : Cyl.L2v c →L[ℝ] ℝ := innerSL ℝ (Cyl.gradL hψ)
      change Lψ (∫ r in a..t, uL2 c Fin.elim0 w1 r) = 0
      rw [← Lψ.intervalIntegral_comp_comm hint_w1]
      have hzero_on : ∀ r ∈ uIcc a t, Lψ (uL2 c Fin.elim0 w1 r) = 0 :=
        fun r hr => Cyl.mem_divFree.mp (hw1_divFree (huIcc hr)) ψ hψ
      rw [intervalIntegral.integral_congr hzero_on]
      simp
    have hΔ_divFree : Δ ∈ Cyl.divFree c :=
      (Cyl.divFree c).sub_mem ((Cyl.divFree c).sub_mem (hw_divFree ht) (hw_divFree ha))
        hint_mem_divFree
    -- Show `Δ` is orthogonal to every solenoidal test field `Φ`
    refine eq_zero_of_divFree_and_ortho_solTest hc Δ hΔ_divFree fun Φ hΦ => ?_
    obtain ⟨_, hwk_eq⟩ := F8Ex.weak_eq_sub_of_slices hdat hwk hsp ha ht hΦ
    let Φ_lp : Cyl.L2v c := toLpCell (F8Ex.memLp_realSolCylTest hΦ)
    let LΦ : Cyl.L2v c →L[ℝ] ℝ := innerSL ℝ Φ_lp
    have hΦ_div : Φ_lp ∈ Cyl.divFree c := toLpCell_realSolCylTest_mem_divFree hc hΦ
    -- Identify `F_sp r = -⟪Φ_lp, uL2 c Fin.elim0 w1 r⟫_ℝ` for `r ∈ Ioo 0 2`
    have hF_sp_eq : ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 2 →
        (∫ y in B0579.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
              B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k)) +
            inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (w r) (F8Ex.slicePdR 0 (w r))
              (F8Ex.slicePdR 1 (w r)) y))) =
        -LΦ (uL2 c Fin.elim0 w1 r) := by
      intro r hr
      -- Viscous term IBP for each component `k : Fin 2`
      have hvisc_k : ∀ k : Fin 2,
          (∫ y in Cyl.cell c,
            (B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
              B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k)) =
          -(∫ y in Cyl.cell c, Φ y k * sliceLapR (w r) y k) := by
        intro k
        have hφk : Sob.IsCylTest c (fun z => Φ z k) := isCylTest_iff_b0579.mpr (hΦ.cyl_test k)
        have hd_φk := hφk.differentiable
        let gq : B0579.Plane → ℝ := fun z => F8Ex.slicePdR 0 (w r) z k
        let ge : B0579.Plane → ℝ := fun z => F8Ex.slicePdR 1 (w r) z k
        have hgq_sm : ContDiff ℝ ∞ gq :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp
            (contDiff_slicePdR (hw_cont.hinf hr).smooth 0)
        have hge_sm : ContDiff ℝ ∞ ge :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp
            (contDiff_slicePdR (hw_cont.hinf hr).smooth 1)
        have hgq_per : Cyl.IsPeriodic c gq := fun z =>
          congrArg (fun v : Cyl.Vec2 => v k)
            (periodic_slicePdR (hw_cont.hinf hr).periodic 0 z)
        have hpQ_gq : Cyl.partialQ gq = fun z => F8Ex.slicePdR 0 (F8Ex.slicePdR 0 (w r)) z k := by
          funext z
          rw [Cyl.partialQ_eq_fderiv (hgq_sm.differentiable (by simp)) z,
            PartI.csb_fderiv_comp_apply
              (((contDiff_slicePdR (hw_cont.hinf hr).smooth 0).differentiable (by simp)) z) k]
          rfl
        have hpE_ge : Cyl.partialEta ge = fun z => F8Ex.slicePdR 1 (F8Ex.slicePdR 1 (w r)) z k := by
          funext z
          rw [Cyl.partialEta_eq_fderiv (hge_sm.differentiable (by simp)) z,
            PartI.csb_fderiv_comp_apply
              (((contDiff_slicePdR (hw_cont.hinf hr).smooth 1).differentiable (by simp)) z) k]
          rfl
        have hm_gq : MemLp gq 2 (Cyl.cellμ c) :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).memL2 1 ![0]))
        have hm_ge : MemLp ge 2 (Cyl.cellμ c) :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).memL2 1 ![1]))
        have hm_dgq : MemLp (Cyl.partialQ gq) 2 (Cyl.cellμ c) := by
          rw [hpQ_gq]
          exact (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).memL2 2 ![0, 0]))
        have hm_dge : MemLp (Cyl.partialEta ge) 2 (Cyl.cellμ c) := by
          rw [hpE_ge]
          exact (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).memL2 2 ![1, 1]))
        have hi_q1 := Cyl.integrableOn_test_mul (Cyl.isCylTest_partialQ hφk) hm_gq
        have hi_q2 := Cyl.integrableOn_test_mul hφk hm_dgq
        have hi_e0 := Cyl.integrableOn_test_mul hφk hm_ge
        have hi_e1 := Cyl.integrableOn_test_mul (Cyl.isCylTest_partialEta hφk) hm_ge
        have hi_e2 := Cyl.integrableOn_test_mul hφk hm_dge
        have hibp_q := Cyl.integral_cell_partialQ_mul hc hd_φk (hgq_sm.differentiable (by simp))
          (fun z => (hΦ.cyl_test k).periodic z) hgq_per hi_q1 hi_q2
        have hibp_e := Cyl.integral_cell_partialEta_mul hd_φk (hge_sm.differentiable (by simp))
          hi_e0 hi_e1 hi_e2
        have hlhs_pt : ∀ y : B0579.Plane,
            B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
              B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k =
            Cyl.partialQ (fun z => Φ z k) y * gq y +
              Cyl.partialEta (fun z => Φ z k) y * ge y := by
          intro y
          rw [Cyl.partialQ_eq_fderiv hd_φk y, Cyl.partialEta_eq_fderiv hd_φk y]
          rfl
        simp_rw [hlhs_pt]
        rw [integral_add hi_q1 hi_e1, hibp_q, hibp_e, ← neg_add, ← integral_add hi_q2 hi_e2]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        rw [hpQ_gq, hpE_ge]
        simp only [sliceLapR, Pi.add_apply, PiLp.add_apply]
        ring
      have hi_bv : IntegrableOn
          (fun y => inner ℝ (Φ y) (bvOp (V r) (w r) y)) (Cyl.cell c) := by
        rw [← b0579_cell_eq_cyl_cell]
        exact F8Ex.integrableOn_innerR_cell (F8Ex.memLp_realSolCylTest hΦ)
          ((hbv_cont.hinf hr).memL2 0 Fin.elim0)
      have hi_visc_k : ∀ k : Fin 2, IntegrableOn
          (fun y => B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
            B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k) (Cyl.cell c) := by
        intro k
        have hφk : Sob.IsCylTest c (fun z => Φ z k) := isCylTest_iff_b0579.mpr (hΦ.cyl_test k)
        have hd_φk := hφk.differentiable
        have hm_gq : MemLp (fun z => F8Ex.slicePdR 0 (w r) z k) 2 (Cyl.cellμ c) :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).memL2 1 ![0]))
        have hm_ge : MemLp (fun z => F8Ex.slicePdR 1 (w r) z k) 2 (Cyl.cellμ c) :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).memL2 1 ![1]))
        have hi1 := Cyl.integrableOn_test_mul (Cyl.isCylTest_partialQ hφk) hm_gq
        have hi2 := Cyl.integrableOn_test_mul (Cyl.isCylTest_partialEta hφk) hm_ge
        refine (hi1.add hi2).congr_fun (fun y _ => ?_) (Cyl.measurableSet_cell c)
        dsimp only [Pi.add_apply]
        rw [Cyl.partialQ_eq_fderiv hd_φk y, Cyl.partialEta_eq_fderiv hd_φk y]
        rfl
      have hi_lap_k : ∀ k : Fin 2,
          IntegrableOn (fun y => Φ y k * sliceLapR (w r) y k) (Cyl.cell c) := by
        intro k
        have hφk : Sob.IsCylTest c (fun z => Φ z k) := isCylTest_iff_b0579.mpr (hΦ.cyl_test k)
        have hm_lk : MemLp (fun z => sliceLapR (w r) z k) 2 (Cyl.cellμ c) :=
          (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
            (memLp_to_cellμ ((hw_cont.hinf hr).sliceLapR.memL2 0 Fin.elim0))
        exact Cyl.integrableOn_test_mul hφk hm_lk
      have hvisc_tot : (∫ y in Cyl.cell c,
          ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
            B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k))) =
          -⟪Φ_lp, ν • toLpCell ((hw_cont.hinf hr).sliceLapR.memL2 0 Fin.elim0)⟫_ℝ := by
        simp_rw [Fin.sum_univ_two]
        rw [integral_const_mul, integral_add (hi_visc_k 0) (hi_visc_k 1),
          hvisc_k 0, hvisc_k 1, inner_smul_right, inner_toLpCell_eq, b0579_cell_eq_cyl_cell]
        have hinner_pt : (∫ y in Cyl.cell c, ⟪Φ y, sliceLapR (w r) y⟫_ℝ) =
            (∫ y in Cyl.cell c, Φ y 0 * sliceLapR (w r) y 0) +
              (∫ y in Cyl.cell c, Φ y 1 * sliceLapR (w r) y 1) := by
          rw [← integral_add (hi_lap_k 0) (hi_lap_k 1)]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp only
          rw [PiLp.inner_apply, Fin.sum_univ_two]
          simp [mul_comm]
        change _ = -(ν * ∫ y in Cyl.cell c, ⟪Φ y, sliceLapR (w r) y⟫_ℝ)
        rw [hinner_pt]
        ring
      have hbv_tot : (∫ y in Cyl.cell c, inner ℝ (Φ y) (bvOp (V r) (w r) y)) =
          ⟪Φ_lp, toLpCell ((P0Smooth_isCylSmoothHInf hc (hbv_cont.hinf hr)).memL2 0 Fin.elim0)⟫_ℝ := by
        rw [toLpCell_P0Smooth hc (hbv_cont.hinf hr), ← Cyl.inner_P0_comm, Cyl.P0_eq_self hΦ_div,
          inner_toLpCell_eq, b0579_cell_eq_cyl_cell]
        rfl
      have hi_visc_tot : IntegrableOn
          (fun y => ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
            B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k))) (Cyl.cell c) := by
        simp only [Fin.sum_univ_two]
        exact ((hi_visc_k 0).add (hi_visc_k 1)).const_mul ν
      rw [b0579_cell_eq_cyl_cell]
      change ∫ y in Cyl.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
            B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k)) +
          inner ℝ (Φ y) (bvOp (V r) (w r) y)) = _
      rw [integral_add hi_visc_tot hi_bv, hvisc_tot, hbv_tot]
      have hw1_eq : uL2 c Fin.elim0 w1 r =
          ν • toLpCell ((hw_cont.hinf hr).sliceLapR.memL2 0 Fin.elim0) -
            toLpCell ((P0Smooth_isCylSmoothHInf hc (hbv_cont.hinf hr)).memL2 0 Fin.elim0) := by
        rw [hw1_cont.uL2_eq Fin.elim0 hr, ← toLpCell_smul, ← toLpCell_sub]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
      change _ = -⟪Φ_lp, uL2 c Fin.elim0 w1 r⟫_ℝ
      rw [hw1_eq, inner_sub_right]
      ring
    have hint_fsp : (∫ r in a..t,
        ∫ y in B0579.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * F8Ex.slicePdR 0 (w r) y k +
              B0579.pd 1 (fun z => Φ z k) y * F8Ex.slicePdR 1 (w r) y k)) +
            inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (w r) (F8Ex.slicePdR 0 (w r))
              (F8Ex.slicePdR 1 (w r)) y))) =
        -LΦ (∫ r in a..t, uL2 c Fin.elim0 w1 r) := by
      have hcongr := intervalIntegral.integral_congr (a := a) (b := t) (μ := volume)
        (fun r hr => hF_sp_eq (huIcc hr))
      rw [hcongr, intervalIntegral.integral_neg, LΦ.intervalIntegral_comp_comm hint_w1]
    have hdiff_phi : (∫ y in B0579.cell c, inner ℝ (Φ y) (w t y - w a y)) =
        LΦ (uL2 c Fin.elim0 w t - uL2 c Fin.elim0 w a) := by
      change _ = ⟪Φ_lp, uL2 c Fin.elim0 w t - uL2 c Fin.elim0 w a⟫_ℝ
      rw [hw_cont.uL2_eq Fin.elim0 ht, hw_cont.uL2_eq Fin.elim0 ha, ← toLpCell_sub,
        inner_toLpCell_eq]
      rfl
    rw [hdiff_phi, hint_fsp, map_sub] at hwk_eq
    change LΦ Δ = 0
    simp only [Δ, map_sub]
    linarith
  exact
    { u_cont := hw_cont
      u'_cont := hw1_cont
      hasDeriv := fun {n} α {s} hs =>
        hasDerivAt_of_sub_eq_intervalIntegral (hw1_cont.cont α)
          (fun {a t} ha ht => sub_eq_intervalIntegral_all hc n hw_cont hw1_cont h0_int α ha ht)
          hs }

/-! ## 5. Full `H^∞(C_c)` Time-Derivative Tower `wSeq` and Subinterval `BwdRoute.Joint.Tower` -/

/-- Pointwise sum of a list of time-indexed meridional slice curves. -/
def listSumSlice : List (ℝ → B0579.Plane → F8Ex.RMerid) → ℝ → B0579.Plane → F8Ex.RMerid
  | [] => fun _ => 0
  | u :: us => fun s => u s + listSumSlice us s

lemma listSumSlice_append (l₁ l₂ : List (ℝ → B0579.Plane → F8Ex.RMerid)) (s : ℝ) :
    listSumSlice (l₁ ++ l₂) s = listSumSlice l₁ s + listSumSlice l₂ s := by
  induction l₁ with
  | nil => simp [listSumSlice]
  | cons u us ih =>
      simp only [List.cons_append, listSumSlice, ih]
      funext y
      simp only [Pi.add_apply]
      abel

lemma hasHInfDerivOn_listSumSlice {c : ℝ} :
    ∀ {us us' : List (ℝ → B0579.Plane → F8Ex.RMerid)},
      List.Forall₂ (HasHInfDerivOn c) us us' →
      HasHInfDerivOn c (listSumSlice us) (listSumSlice us')
  | _, _, List.Forall₂.nil => HasHInfDerivOn.zero c
  | _, _, List.Forall₂.cons hd hrest =>
      hd.add (hasHInfDerivOn_listSumSlice hrest)

/-- Formal index pairs `(j, i)` (`j : ℕ`, `i : Fin (m + 1)`) for the `m`-th time derivative of
`P0Smooth c (bvOp (V s) (w s))`. -/
def advIdx : (m : ℕ) → List (ℕ × Fin (m + 1))
  | 0 => [(0, 0)]
  | m + 1 =>
      (advIdx m).flatMap fun p =>
        [(p.1 + 1, p.2.castSucc), (p.1, p.2.succ)]

/-- History tuple `(w_0, …, w_m)` of successive time derivatives of `w` on `(0, 2)`. -/
def wHist (c ν : ℝ) (V : ℝ → B0579.Plane → F8Ex.RMerid)
    (w : ℝ → B0579.Plane → F8Ex.RMerid) :
    (m : ℕ) → Fin (m + 1) → ℝ → B0579.Plane → F8Ex.RMerid
  | 0 => fun _ => w
  | m + 1 =>
      let prev := wHist c ν V w m
      Fin.snoc prev fun s =>
        ν • sliceLapR (prev (Fin.last m) s) -
          listSumSlice ((advIdx m).map fun p s' => P0Smooth c (bvOp (dtIterV p.1 V s') (prev p.2 s'))) s

lemma wHist_succ_castSucc (c ν : ℝ) (V w : ℝ → B0579.Plane → F8Ex.RMerid)
    (m : ℕ) (i : Fin (m + 1)) :
    wHist c ν V w (m + 1) i.castSucc = wHist c ν V w m i := by
  dsimp only [wHist]
  rw [Fin.snoc_castSucc]

lemma wHist_succ_last (c ν : ℝ) (V w : ℝ → B0579.Plane → F8Ex.RMerid) (m : ℕ) :
    wHist c ν V w (m + 1) (Fin.last (m + 1)) =
      fun s => ν • sliceLapR (wHist c ν V w m (Fin.last m) s) -
        listSumSlice ((advIdx m).map fun p s' =>
          P0Smooth c (bvOp (dtIterV p.1 V s') (wHist c ν V w m p.2 s'))) s := by
  dsimp only [wHist]
  rw [Fin.snoc_last]

/-- The infinite tower `wSeq m := wHist c ν V w m (Fin.last m)` of successive time derivatives. -/
def wSeq (c ν : ℝ) (V : ℝ → B0579.Plane → F8Ex.RMerid)
    (w : ℝ → B0579.Plane → F8Ex.RMerid) (m : ℕ) : ℝ → B0579.Plane → F8Ex.RMerid :=
  wHist c ν V w m (Fin.last m)

@[simp]
lemma wSeq_zero (c ν : ℝ) (V : ℝ → B0579.Plane → F8Ex.RMerid)
    (w : ℝ → B0579.Plane → F8Ex.RMerid) :
    wSeq c ν V w 0 = w := rfl

lemma wSeq_one_eq (c ν : ℝ) (V : ℝ → B0579.Plane → F8Ex.RMerid)
    (w : ℝ → B0579.Plane → F8Ex.RMerid) (s : ℝ) :
    wSeq c ν V w 1 s =
      ν • sliceLapR (w s) - P0Smooth c (bvOp (V s) (w s)) := by
  unfold wSeq
  rw [wHist_succ_last]
  simp only [wHist, advIdx, List.map_cons, List.map_nil, listSumSlice, dtIterV_zero, add_zero]

private lemma hasHInfDerivOn_advList {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {m : ℕ} {hist : Fin (m + 2) → ℝ → B0579.Plane → F8Ex.RMerid}
    (hh : ∀ i : Fin (m + 1), HasHInfDerivOn c (hist i.castSucc) (hist i.succ)) :
    ∀ l : List (ℕ × Fin (m + 1)),
      HasHInfDerivOn c
        (listSumSlice (l.map fun p s =>
          P0Smooth c (bvOp (dtIterV p.1 (F8Ex.shiftedDriftTrain tr σ) s) (hist p.2.castSucc s))))
        (listSumSlice ((l.flatMap fun p => [(p.1 + 1, p.2.castSucc), (p.1, p.2.succ)]).map
          fun q s => P0Smooth c (bvOp (dtIterV q.1 (F8Ex.shiftedDriftTrain tr σ) s) (hist q.2 s))))
  | [] => HasHInfDerivOn.zero c
  | p :: ps => by
      let V := F8Ex.shiftedDriftTrain tr σ
      have ih := hasHInfDerivOn_advList hc hν tr hbuc hσ hh ps
      have hd_p := ((hh p.2).bvOp_dtIterV hc hν tr hbuc hσ p.1).P0Smooth hc
      have hd_p' : HasHInfDerivOn c
          (fun s => P0Smooth c (bvOp (dtIterV p.1 V s) (hist p.2.castSucc s)))
          (fun s => P0Smooth c (bvOp (dtIterV (p.1 + 1) V s) (hist p.2.castSucc s)) +
            P0Smooth c (bvOp (dtIterV p.1 V s) (hist p.2.succ s))) := by
        refine hasHInfDerivOn_congr hd_p (fun _ => rfl) fun {s} hs => ?_
        have h1 := ((hh p.2).u_cont.bvOp_dtIterV hc hν tr hbuc hσ (p.1 + 1)).hinf hs
        have h2 := ((hh p.2).u'_cont.bvOp_dtIterV hc hν tr hbuc hσ p.1).hinf hs
        exact P0Smooth_add hc h1 h2
      have hcomb := hd_p'.add ih
      refine hasHInfDerivOn_congr hcomb (fun _ => rfl) fun {s} _ => ?_
      simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
        listSumSlice_append, listSumSlice]
      funext y
      simp only [Pi.add_apply, add_zero]
      abel

private lemma wHist_hasHInfDerivOn {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη) :
    ∀ (m : ℕ) (i : Fin (m + 1)),
      HasHInfDerivOn c
        (wHist c ν (F8Ex.shiftedDriftTrain tr σ) w (m + 1) i.castSucc)
        (wHist c ν (F8Ex.shiftedDriftTrain tr σ) w (m + 1) i.succ)
  | 0, i => by
      have hi0 : i = 0 := Fin.eq_zero i
      subst hi0
      have hbase := hasHInfDerivOn_w hc hν tr hbuc hσ hdat hwk hsp
      refine hasHInfDerivOn_congr hbase
        (fun _ => by rw [wHist_succ_castSucc]; rfl)
        (fun {s} _ => ?_)
      have h1 : wHist c ν (F8Ex.shiftedDriftTrain tr σ) w 1 ((0 : Fin 1).succ) s =
          wSeq c ν (F8Ex.shiftedDriftTrain tr σ) w 1 s := rfl
      rw [h1, wSeq_one_eq]
  | m + 1, i => by
      let V := F8Ex.shiftedDriftTrain tr σ
      have ih : ∀ j : Fin (m + 1),
          HasHInfDerivOn c (wHist c ν V w (m + 1) j.castSucc) (wHist c ν V w (m + 1) j.succ) :=
        wHist_hasHInfDerivOn hc hν tr hbuc hσ hdat hwk hsp m
      refine Fin.lastCases ?_ (fun j => ?_) i
      · -- New top step `i = Fin.last (m + 1)`
        rw [wHist_succ_castSucc c ν V w (m + 1), Fin.succ_last, wHist_succ_last c ν V w (m + 1)]
        have hd_prev : HasHInfDerivOn c
            (wHist c ν V w m (Fin.last m))
            (wHist c ν V w (m + 1) (Fin.last (m + 1))) := by
          have hlast := ih (Fin.last m)
          rwa [wHist_succ_castSucc, Fin.succ_last] at hlast
        have hd_visc := (hd_prev.sliceLapR).smul ν
        have hd_adv := hasHInfDerivOn_advList hc hν tr hbuc hσ ih (advIdx m)
        have hd_tot := hd_visc.sub hd_adv
        refine hasHInfDerivOn_congr hd_tot (fun {s} _ => ?_) (fun _ => rfl)
        rw [wHist_succ_last c ν V w m]
        have hmap_eq : ((advIdx m).map fun p s' =>
            P0Smooth c (bvOp (dtIterV p.1 V s') (wHist c ν V w (m + 1) p.2.castSucc s'))) =
            ((advIdx m).map fun p s' =>
              P0Smooth c (bvOp (dtIterV p.1 V s') (wHist c ν V w m p.2 s'))) := by
          refine List.map_congr_left fun p _ => ?_
          funext s'
          rw [wHist_succ_castSucc c ν V w m]
        rw [hmap_eq]
      · -- Earlier step `i = j.castSucc`
        rw [wHist_succ_castSucc c ν V w (m + 1), ← Fin.castSucc_succ,
          wHist_succ_castSucc c ν V w (m + 1)]
        exact ih j

/-- **Main export 1 of `TimeTower.lean`**: every level `m` of `wSeq` has `H^∞(C_c)` time derivative
`wSeq (m + 1)` on `(0, 2)`. -/
theorem hasHInfDerivOn_wSeq {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη) (m : ℕ) :
    HasHInfDerivOn c
      (wSeq c ν (F8Ex.shiftedDriftTrain tr σ) w m)
      (wSeq c ν (F8Ex.shiftedDriftTrain tr σ) w (m + 1)) := by
  have h := wHist_hasHInfDerivOn hc hν tr hbuc hσ hdat hwk hsp m (Fin.last m)
  rw [wHist_succ_castSucc, Fin.succ_last] at h
  exact h

/-- **Main export 2 of `TimeTower.lean`**: on every compact subinterval `[T₁, T₂] ⊂ (0, 2)` and
each meridional component `k : Fin 2`, the shifted sequence `m ↦ (r, y) ↦ wSeq ... m (T₁ + r) y k`
forms a `BwdRoute.Joint.Tower (T₂ - T₁)`. -/
theorem tower_wSeq_on_subinterval {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₁₂ : T₁ < T₂) (hT₂ : T₂ < 2) (k : Fin 2) :
    BwdRoute.Joint.Tower (T₂ - T₁)
      (fun m r y => wSeq c ν (F8Ex.shiftedDriftTrain tr σ) w m (T₁ + r) y k) where
  sp m := ((hasHInfDerivOn_wSeq hc hν tr hbuc hσ hdat hwk hsp m).u_cont).spSmooth hc hT₁ hT₁₂ hT₂ k
  dt m := (hasHInfDerivOn_wSeq hc hν tr hbuc hσ hdat hwk hsp m).hasTimeDeriv hc hT₁ hT₁₂ hT₂ k

end UnforcedLeray.Short.IIb.F8JointUpgrade
