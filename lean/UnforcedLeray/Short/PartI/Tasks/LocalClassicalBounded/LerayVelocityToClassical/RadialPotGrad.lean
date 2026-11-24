import UnforcedLeray.Short.PartI.Sub.T02_1_5

/-!
# Part I, task `PartI:T02/1/5/5` (Leaf 5): the Poincare lemma on the plane

Source of record: `the November 2 reference manuscript`, lines 261-288.
This file proves `RadialPotGrad` (defined in `Short/PartI/Sub/T02_1_5.lean`): for a smooth
curl-free field `G` on the plane, `gradS (radialPot G) = -G`.

Method.  Write `rpgI G q η t = q * G₀(t·(q,η)) + η * G₁(t·(q,η))`, so that
`radialPot G (q,η) = -∫₀¹ rpgI G q η t dt`.  Differentiating under the integral sign in `q`
(resp. `η`) gives the integrands `rpgD` (resp. `rpgE`).  The curl identity `∂₁G₁ = ∂₂G₀`
turns these into `d/dt [t G₀(t·x)]` (resp. `d/dt [t G₁(t·x)]`), and the fundamental theorem of
calculus on `[0,1]` gives `G₀(x)` (resp. `G₁(x)`).  Derivatives of `G` are written with `fderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The integrand of `radialPot G (q, η) = -∫₀¹ rpgI G q η t dt`. -/
def rpgI (G : Plane → Vec) (q η t : ℝ) : ℝ :=
  q * G (t • (q, η)) 0 + η * G (t • (q, η)) 1

/-- The `q`-derivative of `rpgI G · η t`, written with `fderiv`. -/
def rpgD (G : Plane → Vec) (q η t : ℝ) : ℝ :=
  G (t • (q, η)) 0 +
    t * (q * fderiv ℝ G (t • (q, η)) (1, 0) 0 + η * fderiv ℝ G (t • (q, η)) (0, 1) 0)

/-- The `η`-derivative of `rpgI G q · t`, written with `fderiv`. -/
def rpgE (G : Plane → Vec) (q η t : ℝ) : ℝ :=
  G (t • (q, η)) 1 +
    t * (q * fderiv ℝ G (t • (q, η)) (1, 0) 1 + η * fderiv ℝ G (t • (q, η)) (0, 1) 1)

/-! ### Calculus helpers -/

lemma rpg_cont_coord {X : Type*} [TopologicalSpace X] {f : X → Vec} (hf : Continuous f)
    (i : Fin 2) : Continuous fun p => f p i := by
  fun_prop

lemma rpg_hasDerivAt_proj {f : ℝ → Vec} {f' : Vec} {s : ℝ} (h : HasDerivAt f f' s) (i : Fin 2) :
    HasDerivAt (fun u => f u i) (f' i) s := by
  have h2 := ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt s h
  simpa [Function.comp_def] using h2

lemma rpg_hasDerivAt_comp {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) {p : ℝ → Plane} {p' : Plane}
    {s : ℝ} (h : HasDerivAt p p' s) : HasDerivAt (fun u => G (p u)) (fderiv ℝ G (p s) p') s :=
  ((hG.differentiable (by simp) (p s)).hasFDerivAt).comp_hasDerivAt s h

lemma rpg_decomp (G : Plane → Vec) (w : Plane) (a b : ℝ) (i : Fin 2) :
    fderiv ℝ G w (a, b) i = a * fderiv ℝ G w (1, 0) i + b * fderiv ℝ G w (0, 1) i := by
  have h : ((a, b) : Plane) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

lemma rpg_partialQ_comp {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (i : Fin 2) (z : Plane) :
    Cyl.partialQ (fun w => G w i) z = fderiv ℝ G z (1, 0) i := by
  obtain ⟨a, b⟩ := z
  have hp : HasDerivAt (fun u : ℝ => (u, b)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id' a).prodMk (hasDerivAt_const a b)
  exact (rpg_hasDerivAt_proj (rpg_hasDerivAt_comp hG hp) i).deriv

lemma rpg_partialEta_comp {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (i : Fin 2) (z : Plane) :
    Cyl.partialEta (fun w => G w i) z = fderiv ℝ G z (0, 1) i := by
  obtain ⟨a, b⟩ := z
  have hp : HasDerivAt (fun u : ℝ => (a, u)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id' b)
  exact (rpg_hasDerivAt_proj (rpg_hasDerivAt_comp hG hp) i).deriv

/-! ### Joint continuity of the integrands -/

lemma rpg_cont_eval_G {X : Type*} [TopologicalSpace X] {G : Plane → Vec} (hG : Continuous G)
    {m : X → Plane} (hm : Continuous m) (i : Fin 2) : Continuous fun p => G (m p) i :=
  rpg_cont_coord (hG.comp hm) i

lemma rpg_cont_eval_D {X : Type*} [TopologicalSpace X] {G : Plane → Vec}
    (hD : Continuous (fderiv ℝ G)) {m : X → Plane} (hm : Continuous m) (v : Plane) (i : Fin 2) :
    Continuous fun p => fderiv ℝ G (m p) v i :=
  rpg_cont_coord ((hD.comp hm).clm_apply (continuous_const : Continuous fun _ : X => v)) i

lemma rpg_cont_I_q {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (η : ℝ) :
    Continuous fun p : ℝ × ℝ => rpgI G p.1 η p.2 := by
  have hm : Continuous fun p : ℝ × ℝ => p.2 • (p.1, η) :=
    continuous_snd.smul (continuous_fst.prodMk continuous_const)
  unfold rpgI
  exact (continuous_fst.mul (rpg_cont_eval_G hG.continuous hm 0)).add
    (continuous_const.mul (rpg_cont_eval_G hG.continuous hm 1))

lemma rpg_cont_D_q {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (η : ℝ) :
    Continuous fun p : ℝ × ℝ => rpgD G p.1 η p.2 := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  have hm : Continuous fun p : ℝ × ℝ => p.2 • (p.1, η) :=
    continuous_snd.smul (continuous_fst.prodMk continuous_const)
  unfold rpgD
  exact (rpg_cont_eval_G hG.continuous hm 0).add
    (continuous_snd.mul ((continuous_fst.mul (rpg_cont_eval_D hD hm (1, 0) 0)).add
      (continuous_const.mul (rpg_cont_eval_D hD hm (0, 1) 0))))

lemma rpg_cont_I_e {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (q : ℝ) :
    Continuous fun p : ℝ × ℝ => rpgI G q p.1 p.2 := by
  have hm : Continuous fun p : ℝ × ℝ => p.2 • (q, p.1) :=
    continuous_snd.smul (continuous_const.prodMk continuous_fst)
  unfold rpgI
  exact (continuous_const.mul (rpg_cont_eval_G hG.continuous hm 0)).add
    (continuous_fst.mul (rpg_cont_eval_G hG.continuous hm 1))

lemma rpg_cont_E {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (q : ℝ) :
    Continuous fun p : ℝ × ℝ => rpgE G q p.1 p.2 := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  have hm : Continuous fun p : ℝ × ℝ => p.2 • (q, p.1) :=
    continuous_snd.smul (continuous_const.prodMk continuous_fst)
  unfold rpgE
  exact (rpg_cont_eval_G hG.continuous hm 1).add
    (continuous_snd.mul ((continuous_const.mul (rpg_cont_eval_D hD hm (1, 0) 1)).add
      (continuous_fst.mul (rpg_cont_eval_D hD hm (0, 1) 1))))

/-! ### Pointwise derivatives of the integrands -/

lemma rpg_hasDerivAt_I_q {G : Plane → Vec} (hG : ContDiff ℝ ∞ G)
    (hc : ∀ w : Plane, fderiv ℝ G w (1, 0) 1 = fderiv ℝ G w (0, 1) 0) (η t u : ℝ) :
    HasDerivAt (fun v : ℝ => rpgI G v η t) (rpgD G u η t) u := by
  have hp : HasDerivAt (fun v : ℝ => t • (v, η)) (t • ((1 : ℝ), (0 : ℝ))) u :=
    ((hasDerivAt_id' u).prodMk (hasDerivAt_const u η)).const_smul t
  have hg := rpg_hasDerivAt_comp hG hp
  have hsum := ((hasDerivAt_id' u).mul (rpg_hasDerivAt_proj hg 0)).add
    ((hasDerivAt_const u η).mul (rpg_hasDerivAt_proj hg 1))
  unfold rpgI rpgD
  refine hsum.congr_deriv ?_
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [hc]
  ring

lemma rpg_hasDerivAt_I_e {G : Plane → Vec} (hG : ContDiff ℝ ∞ G)
    (hc : ∀ w : Plane, fderiv ℝ G w (1, 0) 1 = fderiv ℝ G w (0, 1) 0) (q t u : ℝ) :
    HasDerivAt (fun v : ℝ => rpgI G q v t) (rpgE G q u t) u := by
  have hp : HasDerivAt (fun v : ℝ => t • (q, v)) (t • ((0 : ℝ), (1 : ℝ))) u :=
    ((hasDerivAt_const u q).prodMk (hasDerivAt_id' u)).const_smul t
  have hg := rpg_hasDerivAt_comp hG hp
  have hsum := ((hasDerivAt_const u q).mul (rpg_hasDerivAt_proj hg 0)).add
    ((hasDerivAt_id' u).mul (rpg_hasDerivAt_proj hg 1))
  unfold rpgI rpgE
  refine hsum.congr_deriv ?_
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [← hc]
  ring

/-! ### Fundamental theorem of calculus on `[0,1]` -/

lemma rpg_hasDerivAt_s_D {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (q η s : ℝ) :
    HasDerivAt (fun r : ℝ => r * G (r • (q, η)) 0) (rpgD G q η s) s := by
  have hp : HasDerivAt (fun r : ℝ => r • (q, η)) (q, η) s := by
    have h := (hasDerivAt_id' s).smul_const ((q, η) : Plane)
    rwa [one_smul] at h
  have hsum := (hasDerivAt_id' s).mul (rpg_hasDerivAt_proj (rpg_hasDerivAt_comp hG hp) 0)
  unfold rpgD
  refine hsum.congr_deriv ?_
  rw [rpg_decomp G (s • (q, η)) q η 0]
  ring

lemma rpg_hasDerivAt_s_E {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (q η s : ℝ) :
    HasDerivAt (fun r : ℝ => r * G (r • (q, η)) 1) (rpgE G q η s) s := by
  have hp : HasDerivAt (fun r : ℝ => r • (q, η)) (q, η) s := by
    have h := (hasDerivAt_id' s).smul_const ((q, η) : Plane)
    rwa [one_smul] at h
  have hsum := (hasDerivAt_id' s).mul (rpg_hasDerivAt_proj (rpg_hasDerivAt_comp hG hp) 1)
  unfold rpgE
  refine hsum.congr_deriv ?_
  rw [rpg_decomp G (s • (q, η)) q η 1]
  ring

lemma rpg_ftc_D {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (q η : ℝ) :
    ∫ t in (0 : ℝ)..1, rpgD G q η t = G (q, η) 0 := by
  have hqt : Continuous fun t : ℝ => ((q, t) : ℝ × ℝ) := continuous_const.prodMk continuous_id
  have hcont : Continuous fun t : ℝ => rpgD G q η t := (rpg_cont_D_q hG η).comp hqt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => rpg_hasDerivAt_s_D hG q η s)
    (hcont.intervalIntegrable 0 1)]
  simp

lemma rpg_ftc_E {G : Plane → Vec} (hG : ContDiff ℝ ∞ G) (q η : ℝ) :
    ∫ t in (0 : ℝ)..1, rpgE G q η t = G (q, η) 1 := by
  have hηt : Continuous fun t : ℝ => ((η, t) : ℝ × ℝ) := continuous_const.prodMk continuous_id
  have hcont : Continuous fun t : ℝ => rpgE G q η t := (rpg_cont_E hG q).comp hηt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => rpg_hasDerivAt_s_E hG q η s)
    (hcont.intervalIntegrable 0 1)]
  simp

/-! ### Differentiation under the integral sign on `[0,1]` -/

lemma rpg_dominated {F F' : ℝ → ℝ → ℝ} (x0 : ℝ)
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hF' : Continuous fun p : ℝ × ℝ => F' p.1 p.2)
    (hderiv : ∀ u t : ℝ, HasDerivAt (fun v => F v t) (F' u t) u) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..1, F u t) (∫ t in (0 : ℝ)..1, F' x0 t) x0 := by
  have hcomp : ∀ u : ℝ, Continuous fun t : ℝ => ((u, t) : ℝ × ℝ) :=
    fun u => continuous_const.prodMk continuous_id
  have hut : ∀ u : ℝ, Continuous fun t : ℝ => F u t := fun u => hF.comp (hcomp u)
  have hut' : ∀ u : ℝ, Continuous fun t : ℝ => F' u t := fun u => hF'.comp (hcomp u)
  have hK : IsCompact (Icc (x0 - 1) (x0 + 1) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuousOn
  have hs : Ioo (x0 - 1) (x0 + 1) ∈ 𝓝 x0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ u in 𝓝 x0,
      AEStronglyMeasurable (fun t => F u t) (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    Eventually.of_forall (fun u => (hut u).aestronglyMeasurable)
  have hint : IntervalIntegrable (fun t => F x0 t) volume 0 1 :=
    (hut x0).intervalIntegrable 0 1
  have hmeas' : AEStronglyMeasurable (fun t => F' x0 t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    (hut' x0).aestronglyMeasurable
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ u ∈ Ioo (x0 - 1) (x0 + 1), ‖F' u t‖ ≤ C := by
    refine ae_of_all _ (fun t ht u hu => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hmem : (u, t) ∈ Icc (x0 - 1) (x0 + 1) ×ˢ Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod ⟨hu.1.le, hu.2.le⟩ ⟨ht.1.le, ht.2⟩
    exact hC (u, t) hmem
  have hbi : IntervalIntegrable (fun _ : ℝ => C) volume 0 1 := intervalIntegrable_const
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ u ∈ Ioo (x0 - 1) (x0 + 1), HasDerivAt (fun v => F v t) (F' u t) u :=
    ae_of_all _ (fun t _ u _ => hderiv u t)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : ℝ => C) hs hmeas hint hmeas' hb hbi hdiff
  exact key.2

/-! ### The two partial derivatives of `radialPot` -/

lemma rpg_slopeQ {G : Plane → Vec} (hG : ContDiff ℝ ∞ G)
    (hc : ∀ w : Plane, fderiv ℝ G w (1, 0) 1 = fderiv ℝ G w (0, 1) 0) (q η : ℝ) :
    HasDerivAt (fun v : ℝ => radialPot G (v, η)) (-(G (q, η) 0)) q := by
  have hI : HasDerivAt (fun u => ∫ t in (0 : ℝ)..1, rpgI G u η t)
      (∫ t in (0 : ℝ)..1, rpgD G q η t) q :=
    rpg_dominated (F := fun u t => rpgI G u η t) (F' := fun u t => rpgD G u η t) q
      (rpg_cont_I_q hG η) (rpg_cont_D_q hG η) (fun u t => rpg_hasDerivAt_I_q hG hc η t u)
  rw [rpg_ftc_D hG q η] at hI
  exact hI.neg

lemma rpg_slopeE {G : Plane → Vec} (hG : ContDiff ℝ ∞ G)
    (hc : ∀ w : Plane, fderiv ℝ G w (1, 0) 1 = fderiv ℝ G w (0, 1) 0) (q η : ℝ) :
    HasDerivAt (fun v : ℝ => radialPot G (q, v)) (-(G (q, η) 1)) η := by
  have hI : HasDerivAt (fun v => ∫ t in (0 : ℝ)..1, rpgI G q v t)
      (∫ t in (0 : ℝ)..1, rpgE G q η t) η :=
    rpg_dominated (F := fun v t => rpgI G q v t) (F' := fun u t => rpgE G q u t) η
      (rpg_cont_I_e hG q) (rpg_cont_E hG q) (fun u t => rpg_hasDerivAt_I_e hG hc q t u)
  rw [rpg_ftc_E hG q η] at hI
  exact hI.neg

/-! ### Leaf 5 -/

/-- **Leaf 5** (the Poincare lemma on the plane): for a smooth curl-free field `G`,
`∇(radialPot G) = -G`. -/
theorem radialPotGrad : RadialPotGrad := by
  unfold RadialPotGrad
  intro G hG hcurl z
  have hc : ∀ w : Plane, fderiv ℝ G w (1, 0) 1 = fderiv ℝ G w (0, 1) 0 := by
    intro w
    have h := hcurl w
    rw [rpg_partialQ_comp hG 1 w, rpg_partialEta_comp hG 0 w] at h
    exact h
  obtain ⟨q0, η⟩ := z
  have h1 : Cyl.partialQ (radialPot G) (q0, η) = -(G (q0, η) 0) :=
    (rpg_slopeQ hG hc q0 η).deriv
  have h2 : Cyl.partialEta (radialPot G) (q0, η) = -(G (q0, η) 1) :=
    (rpg_slopeE hG hc q0 η).deriv
  unfold Train.gradS
  rw [h1, h2, Train.eq_toVec (-(G (q0, η)))]
  simp

end UnforcedLeray.Short.PartI
