import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit

/-!
# `PartIII-a:T21/2/3/1/9/2` (`LadTranspLimit`), audit repair

Source: `the November 2 reference manuscript` (SP) lines 3052-3058.

`LadTranspLimit` (in `PartIII-a_T21_2_3_1_9.lean`) takes the velocities `ua_n, ub_n` as free
functions: the Bochner integral `∫ φ (ua_n·∇E)` is `0` when the integrand is not a.e. strongly
measurable, so the identity hypotheses carry no information for non-measurable `ua_n` and the
statement is not provable as written.  `LadTranspLimitM` adds the (true, supplied by
`IsKernelBiotSavart`) a.e. measurability of the velocities.  We prove `LadTranspLimitM` and
`ladTransposition_of_M`, the version of `ladTransposition_of` with the measurable leaf.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- `LadTranspLimit` with the a.e. measurability of the approximating velocities. -/
def LadTranspLimitM (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (w : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ → ρ ∈ Ioo t s →
    MemLp w 2 (B0579.cellMeasure c m) → IsBiotSavart c w u →
    MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) →
    ∀ (a b : ℕ → ℝ × ℝ → ℝ) (ua ub : ℕ → ℝ × ℝ → Fin 2 → ℝ),
      (∀ n, B0579.IsCylTest c (a n) ∧ B0579.IsCylTest c (b n)) →
      (∀ n (j : Fin 2), AEStronglyMeasurable (fun x => ua n x j) (volume.restrict (B0579.cell c)) ∧
        AEStronglyMeasurable (fun x => ub n x j) (volume.restrict (B0579.cell c))) →
      (∀ n, ∫ x in B0579.cell c, ladChi tr φ ρ x * ((a n x : ℝ) : ℂ) =
        ∫ x in B0579.cell c, φ ρ x *
          ((ua n x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
            ua n x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) →
      (∀ n, ∫ x in B0579.cell c, ladChi tr φ ρ x * ((b n x : ℝ) : ℂ) =
        ∫ x in B0579.cell c, φ ρ x *
          ((ub n x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
            ub n x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) →
      Tendsto (fun n => xNorm c m
        (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0) →
      (∀ j : Fin 2, Tendsto (fun n => eLpNorm
        (fun x => ((ua n x j : ℝ) : ℂ) + Complex.I * ((ub n x j : ℝ) : ℂ) - u x j) 2
          (volume.restrict (B0579.cell c))) atTop (𝓝 0)) →
      ∫ x in B0579.cell c, w x * ladChi tr φ ρ x =
        ∫ x in B0579.cell c, ladForce tr u ρ x * φ ρ x

namespace TranspLimitAux

/-- Pairing against a fixed `X_{-m}` function is continuous for `X_m` convergence. -/
lemma pairing_tendsto {c m : ℝ} {A : ℕ → ℝ × ℝ → ℂ} {w χ : ℝ × ℝ → ℂ}
    (hA : ∀ n, MemLp (A n) 2 (B0579.cellMeasure c m)) (hw : MemLp w 2 (B0579.cellMeasure c m))
    (hχ : MemLp χ 2 (B0579.cellMeasure c (-m)))
    (hlim : Tendsto (fun n => eLpNorm (fun x => A n x - w x) 2 (B0579.cellMeasure c m))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in B0579.cell c, A n x * χ x) atTop
      (𝓝 (∫ x in B0579.cell c, w x * χ x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n => (eLpNorm (fun x => A n x - w x) 2
      (B0579.cellMeasure c m)).toReal * (eLpNorm χ 2 (B0579.cellMeasure c (-m))).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).mul_const
      (eLpNorm χ 2 (B0579.cellMeasure c (-m))).toReal
    simpa [Function.comp_def] using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
  have I1 := PairContAux.holder (hA n) hχ
  have I2 := PairContAux.holder hw hχ
  have H := PairContAux.holder ((hA n).sub hw) hχ
  have e : (∫ x in B0579.cell c, A n x * χ x) - (∫ x in B0579.cell c, w x * χ x) =
      ∫ x in B0579.cell c, (A n x - w x) * χ x := by
    rw [← integral_sub I1.1 I2.1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_mul]
  rw [e]
  exact H.2

/-- Real and imaginary parts: finite `L²` distance of `ua + i ub` to `u ∈ L²` plus measurability
gives `ua, ub ∈ L²`. -/
lemma memLp_of_dist {μ : Measure (ℝ × ℝ)} {ua ub : ℝ × ℝ → ℝ} {u : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 μ) (ha : AEStronglyMeasurable ua μ) (hb : AEStronglyMeasurable ub μ)
    (hfin : eLpNorm (fun x => (ua x : ℂ) + Complex.I * (ub x : ℂ) - u x) 2 μ < ⊤) :
    MemLp ua 2 μ ∧ MemLp ub 2 μ := by
  have hD : MemLp (fun x => (ua x : ℂ) + Complex.I * (ub x : ℂ) - u x) 2 μ := by
    refine ⟨?_, hfin⟩
    exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable ha).add
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hb).const_mul Complex.I)).sub hu.1
  have hre : MemLp (fun x => ((ua x : ℂ) + Complex.I * (ub x : ℂ) - u x).re) 2 μ := hD.re
  have him : MemLp (fun x => ((ua x : ℂ) + Complex.I * (ub x : ℂ) - u x).im) 2 μ := hD.im
  have hur : MemLp (fun x => (u x).re) 2 μ := hu.re
  have hui : MemLp (fun x => (u x).im) 2 μ := hu.im
  constructor
  · have e : ua = fun x => ((ua x : ℂ) + Complex.I * (ub x : ℂ) - u x).re + (u x).re := by
      funext x; simp
    rw [e]; exact hre.add hur
  · have e : ub = fun x => ((ua x : ℂ) + Complex.I * (ub x : ℂ) - u x).im + (u x).im := by
      funext x; simp
    rw [e]; exact him.add hui

lemma memLp_D {μ : Measure (ℝ × ℝ)} {ua ub : ℝ × ℝ → ℝ} {u : ℝ × ℝ → ℂ}
    (h1 : MemLp ua 2 μ) (h2 : MemLp ub 2 μ) (hu : MemLp u 2 μ) :
    MemLp (fun x => (ua x : ℂ) + Complex.I * (ub x : ℂ) - u x) 2 μ := by
  have a1 : MemLp (fun x => (ua x : ℂ)) 2 μ := h1.ofReal
  have a2 : MemLp (fun x => (ub x : ℂ)) 2 μ := h2.ofReal
  have a3 : MemLp (fun x => Complex.I * (ub x : ℂ)) 2 μ := a2.const_mul Complex.I
  exact (a1.add a3).sub hu

/-- `ladForce` is additive and homogeneous in the velocity. -/
lemma ladForce_comb {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ)
    (ua ub : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) :
    ladForce tr (fun x j => ((ua x j : ℝ) : ℂ) + Complex.I * ((ub x j : ℝ) : ℂ)) ρ x =
      ladForce tr (fun x j => ((ua x j : ℝ) : ℂ)) ρ x +
        Complex.I * ladForce tr (fun x j => ((ub x j : ℝ) : ℂ)) ρ x := by
  unfold ladForce; ring

lemma ladForce_real {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ)
    (ua : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) :
    ((ua x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
      ua x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ) =
      ladForce tr (fun x j => ((ua x j : ℝ) : ℂ)) ρ x := by
  unfold ladForce; push_cast; ring

end TranspLimitAux

set_option maxHeartbeats 2000000 in
open TranspLimitAux in
theorem ladTranspLimitM_aux (m : ℝ) : LadTranspLimitM m := by
  intro ν c tr t s g φ w u ρ hν hc ht hts hBdd hφ hρ hw hbs hχ a b ua ub hT hmeas hA hB hXn hVn
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  obtain ⟨C, hC⟩ := hBdd ρ hρ0
  have hφρ : MemLp (φ ρ) 2 (B0579.cellMeasure c (-m)) := hφ.memX ρ ⟨hρ.1.le, hρ.2.le⟩
  have hAm : ∀ n, MemLp (fun x => ((a n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    fun n => ((hT n).1.memLp m).ofReal
  have hBm : ∀ n, MemLp (fun x => ((b n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    fun n => ((hT n).2.memLp m).ofReal
  have hAB : ∀ n, MemLp (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c m) := fun n => (hAm n).add ((hBm n).const_mul Complex.I)
  -- left side
  have hL := pairing_tendsto (A := fun n x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ))
    hAB hw hχ hXn
  -- eventual `L²` bounds for the velocities
  have hev : ∀ᶠ n in atTop, ∀ j : Fin 2, eLpNorm
      (fun x => ((ua n x j : ℝ) : ℂ) + Complex.I * ((ub n x j : ℝ) : ℂ) - u x j) 2
        (volume.restrict (B0579.cell c)) < 1 := by
    rw [Filter.eventually_all]
    intro j
    exact (hVn j).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hL2 : ∀ n, N ≤ n → ∀ j : Fin 2,
      MemLp (fun x => ua n x j) 2 (volume.restrict (B0579.cell c)) ∧
        MemLp (fun x => ub n x j) 2 (volume.restrict (B0579.cell c)) := by
    intro n hn j
    exact memLp_of_dist (hbs.1 j) (hmeas n j).1 (hmeas n j).2 ((hN n hn j).trans ENNReal.one_lt_top)
  -- the force densities
  set Fa : ℕ → ℝ × ℝ → ℂ := fun n => ladForce tr (fun x j => ((ua n x j : ℝ) : ℂ)) ρ with hFa
  set Fb : ℕ → ℝ × ℝ → ℂ := fun n => ladForce tr (fun x j => ((ub n x j : ℝ) : ℂ)) ρ with hFb
  have hFam : ∀ n, N ≤ n → MemLp (Fa n) 2 (B0579.cellMeasure c m) := fun n hn =>
    (ladForceMemX m ν c tr ρ C ρ hC ⟨hρ0, le_rfl⟩ _ (fun j => (hL2 n hn j).1.ofReal)).1
  have hFbm : ∀ n, N ≤ n → MemLp (Fb n) 2 (B0579.cellMeasure c m) := fun n hn =>
    (ladForceMemX m ν c tr ρ C ρ hC ⟨hρ0, le_rfl⟩ _ (fun j => (hL2 n hn j).2.ofReal)).1
  have hFm : MemLp (ladForce tr u ρ) 2 (B0579.cellMeasure c m) :=
    (ladForceMemX m ν c tr ρ C ρ hC ⟨hρ0, le_rfl⟩ u hbs.1).1
  -- right side convergence
  have hFn : ∀ n, MemLp (fun x => Fa n x + Complex.I * Fb n x) 2 (B0579.cellMeasure c m) ∨ n < N := by
    intro n
    by_cases hn : N ≤ n
    · exact Or.inl ((hFam n hn).add ((hFbm n hn).const_mul Complex.I))
    · exact Or.inr (not_le.1 hn)
  have hR0 : Tendsto (fun n => eLpNorm (fun x => (Fa (n + N) x + Complex.I * Fb (n + N) x) -
      ladForce tr u ρ x) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) := by
    have hbd : ∀ n, eLpNorm (fun x => (Fa (n + N) x + Complex.I * Fb (n + N) x) -
        ladForce tr u ρ x) 2 (B0579.cellMeasure c m) ≤
        ENNReal.ofReal C * (eLpNorm (fun x => ((ua (n + N) x 0 : ℝ) : ℂ) +
          Complex.I * ((ub (n + N) x 0 : ℝ) : ℂ) - u x 0) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => ((ua (n + N) x 1 : ℝ) : ℂ) +
          Complex.I * ((ub (n + N) x 1 : ℝ) : ℂ) - u x 1) 2 (volume.restrict (B0579.cell c))) := by
      intro n
      have hn : N ≤ n + N := Nat.le_add_left N n
      have hDm : ∀ j : Fin 2, MemLp (fun x => ((ua (n + N) x j : ℝ) : ℂ) +
          Complex.I * ((ub (n + N) x j : ℝ) : ℂ) - u x j) 2 (volume.restrict (B0579.cell c)) :=
        fun j => memLp_D (hL2 _ hn j).1 (hL2 _ hn j).2 (hbs.1 j)
      have := (ladForceMemX m ν c tr ρ C ρ hC ⟨hρ0, le_rfl⟩ _ hDm).2
      refine le_of_eq_of_le ?_ this
      congr 1
      funext x
      simp only [hFa, hFb]
      unfold ladForce
      ring
    have hlim : Tendsto (fun n => ENNReal.ofReal C * (eLpNorm (fun x => ((ua (n + N) x 0 : ℝ) : ℂ) +
          Complex.I * ((ub (n + N) x 0 : ℝ) : ℂ) - u x 0) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => ((ua (n + N) x 1 : ℝ) : ℂ) +
          Complex.I * ((ub (n + N) x 1 : ℝ) : ℂ) - u x 1) 2 (volume.restrict (B0579.cell c))))
        atTop (𝓝 0) := by
      have h0 := (hVn 0).comp (tendsto_add_atTop_nat N)
      have h1 := (hVn 1).comp (tendsto_add_atTop_nat N)
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) (h0.add h1) (Or.inr ENNReal.ofReal_ne_top)
      rw [add_zero, mul_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbd
  have hR := pairing_tendsto (A := fun n x => Fa (n + N) x + Complex.I * Fb (n + N) x)
    (w := ladForce tr u ρ) (χ := φ ρ)
    (fun n => ((hFam (n + N) (Nat.le_add_left N n)).add
      ((hFbm (n + N) (Nat.le_add_left N n)).const_mul Complex.I))) hFm hφρ hR0
  have hL' := hL.comp (tendsto_add_atTop_nat N)
  -- the two sequences agree
  have heq : ∀ n, (∫ x in B0579.cell c,
      (((a (n + N) x : ℝ) : ℂ) + Complex.I * ((b (n + N) x : ℝ) : ℂ)) * ladChi tr φ ρ x) =
      ∫ x in B0579.cell c, (Fa (n + N) x + Complex.I * Fb (n + N) x) * φ ρ x := by
    intro n
    have hn : N ≤ n + N := Nat.le_add_left N n
    have i1 := (PairContAux.holder (hAm (n + N)) hχ).1
    have i2 := (PairContAux.holder (hBm (n + N)) hχ).1
    have j1 := (PairContAux.holder (hFam _ hn) hφρ).1
    have j2 := (PairContAux.holder (hFbm _ hn) hφρ).1
    have e1 : (fun x => (((a (n + N) x : ℝ) : ℂ) + Complex.I * ((b (n + N) x : ℝ) : ℂ)) *
        ladChi tr φ ρ x) = fun x => ladChi tr φ ρ x * ((a (n + N) x : ℝ) : ℂ) +
          Complex.I * (ladChi tr φ ρ x * ((b (n + N) x : ℝ) : ℂ)) := by
      funext x; ring
    have e2 : (fun x => (Fa (n + N) x + Complex.I * Fb (n + N) x) * φ ρ x) =
        fun x => φ ρ x * Fa (n + N) x + Complex.I * (φ ρ x * Fb (n + N) x) := by
      funext x; ring
    have i1' : Integrable (fun x => ladChi tr φ ρ x * ((a (n + N) x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) := by
      exact i1.congr (ae_of_all _ fun x => mul_comm _ _)
    have i2' : Integrable (fun x => ladChi tr φ ρ x * ((b (n + N) x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) := by
      exact i2.congr (ae_of_all _ fun x => mul_comm _ _)
    have j1' : Integrable (fun x => φ ρ x * Fa (n + N) x) (volume.restrict (B0579.cell c)) := by
      exact j1.congr (ae_of_all _ fun x => mul_comm _ _)
    have j2' : Integrable (fun x => φ ρ x * Fb (n + N) x) (volume.restrict (B0579.cell c)) := by
      exact j2.congr (ae_of_all _ fun x => mul_comm _ _)
    rw [e1, e2, integral_add i1' (i2'.const_mul _), integral_add j1' (j2'.const_mul _),
      integral_const_mul, integral_const_mul, hA (n + N), hB (n + N)]
    simp only [hFa, hFb, ← ladForce_real]
  have hfin := tendsto_nhds_unique (hL'.congr heq) hR
  simpa using hfin

/-- The kernel Biot-Savart velocity of a test is a.e. strongly measurable on the cell. -/
lemma aesm_of_kernel {c : ℝ} {ψ : ℝ × ℝ → ℝ} {u : ℝ × ℝ → Fin 2 → ℝ}
    (h : IsKernelBiotSavart c ψ u) (j : Fin 2) :
    AEStronglyMeasurable (fun x => u x j) (volume.restrict (B0579.cell c)) := by
  have h1 := (h.1 j).1
  have h2 : Measurable (fun x : ℝ × ℝ => meanShear c (∫ y in B0579.cell c, ψ y) x j) := by
    unfold meanShear
    by_cases hj : j = 0
    · simp only [hj, ite_true]
      refine measurable_const.mul ?_
      unfold Real.sign
      exact Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const
        (Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
          measurable_const)
    · simp only [hj, ite_false]
      exact measurable_const
  have := h1.add h2.aestronglyMeasurable
  have e : ((fun x => u x j - meanShear c (∫ y in B0579.cell c, ψ y) x j) +
      fun x => meanShear c (∫ y in B0579.cell c, ψ y) x j) = fun x => u x j := by
    funext x; simp
  rwa [e] at this

theorem ladTransposition_of_M (m : ℝ) (hm : 8 < m) (hA : LadTranspApprox m)
    (hL : LadTranspLimitM m) : LadTransposition m := by
  intro ν c tr t s g φ f w u hν hc ht hts hB hφ hf hf0 hflow ρ hρ
  have hz : HasZeroCirculation c (w ρ) :=
    ladFlowZeroCirc m (by linarith) ν c tr t f w u hc hf0 hflow ρ hρ.1.le
  have hmem := hflow.memX ρ hρ.1.le
  have hbs := hflow.biotSavart ρ hρ.1.le
  obtain ⟨a, b, ua, ub, hT, hX, hV⟩ := hA c (w ρ) (u ρ) hc hmem hz hbs
  obtain ⟨M, hM⟩ := ladChiBound_of_weak m (adjWeakChiBound m hm) ν c tr t s g φ hν hc ht hts hB hφ
  have hP := ladAdjPointwise_of_weak m (adjWeakPointwise m)
  refine hL ν c tr t s g φ (w ρ) (u ρ) ρ hν hc ht hts hB hφ hρ hmem hbs (hM ρ hρ).1 a b ua ub
    (fun n => ⟨(hT n).1, (hT n).2.1⟩)
    (fun n j => ⟨aesm_of_kernel (hT n).2.2.1 j, aesm_of_kernel (hT n).2.2.2 j⟩) ?_ ?_ hX hV
  · intro n
    exact hP ν c tr t s g φ hν (by linarith) ht hts hB hφ ρ hρ (a n) (ua n) (hT n).1
      (hT n).2.2.1
  · intro n
    exact hP ν c tr t s g φ hν (by linarith) ht hts hB hφ ρ hρ (b n) (ub n) (hT n).2.1
      (hT n).2.2.2

end UnforcedLeray.Short.IIIa
