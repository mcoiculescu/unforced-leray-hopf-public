import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont.GlobD
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont.GlobE
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.WeakFromSmooth

/-!
# Part III-a: the global part of the cut adjoint rate (`adjGlobContinuous`)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058.

`r ↦ ∫_cell φ(r)(uψ·∇E(r))` is continuous on `(t, s)`. With `w(r) = uψ·∇E(r)`: the train bound
`LadTrainBdd` gives `jb^{m/2}|w(r)| ≤ C jb^{-1}(|uψ₀| + |uψ₁|)`, and this decay function is in `L²`
of the cell (`memLp_decayShear`: `uψ` is an `L²` part plus a bounded mean shear). So `w(r) ∈
X_{m,c}` uniformly, and
`∫ φ(r) w(r) = ∫ (φ(r) - φ(ρ)) w(r) + ∫ φ(ρ) w(r)`: the first term is bounded by
`‖w(r)‖_{X_m} ‖φ(r) - φ(ρ)‖_{X_{-m}} → 0` (`strongCont`, weighted Cauchy-Schwarz `holder`), the
second is continuous by dominated convergence (`∇E` jointly continuous, `GlobEAux.contOn_pd_Ec`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

theorem adjGlobContinuous (m : ℝ) :
    ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
      (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
      ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
        B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
          ContinuousOn (fun r => ∫ x in B0579.cell c, φ r x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) (Ioo t s) := by
  intro ν c tr t s g φ hctx ψ uψ hψ hu
  obtain ⟨hν, hc, ht, hts, hB, hA, hj⟩ := hctx
  obtain ⟨C, hC⟩ := hB s (ht.trans hts.le)
  have hD := memLp_decayShear c (∫ y in B0579.cell c, ψ y) uψ hu.1
  set D : ℝ × ℝ → ℝ := fun x => B0579.jb x ^ (-1 : ℝ) * (|uψ x 0| + |uψ x 1|) with hDdef
  have hD0 : ∀ x, 0 ≤ D x := fun x =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  set w : ℝ → ℝ × ℝ → ℂ := fun r x =>
    ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
      uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) with hwdef
  show ContinuousOn (fun r => ∫ x in B0579.cell c, φ r x * w r x) (Ioo t s)
  have hmeas : MeasurableSet (B0579.cell c) := B0579.measurableSet_cell c
  have hum : ∀ j, AEStronglyMeasurable (fun x => uψ x j) (volume.restrict (B0579.cell c)) :=
    GlobDAux.aesm_vel c _ uψ hu.1
  have hpdc : ∀ r, 0 ≤ r → ∀ j : Fin 2,
      Continuous (B0579.pd j (UnforcedLeray.B0238.Ec tr r)) := fun r hr j =>
    (ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_Ec tr hr) j).continuous
  have hwaesm : ∀ r, 0 ≤ r → AEStronglyMeasurable (w r) (volume.restrict (B0579.cell c)) := by
    intro r hr
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (((hum 0).mul (hpdc r hr 0).aestronglyMeasurable).add
        ((hum 1).mul (hpdc r hr 1).aestronglyMeasurable))
  -- the pointwise train bound
  have hwb : ∀ r ∈ Icc (0 : ℝ) s, ∀ x ∈ B0579.cell c,
      B0579.jb x ^ (m / 2) * ‖w r x‖ ≤ C * D x := by
    intro r hr x hx
    have hbd := hC r hr x hx
    have hw0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hj : ∀ j : Fin 2, B0579.jb x ^ (m / 2) *
        (|uψ x j| * |B0579.pd j (UnforcedLeray.B0238.Ec tr r) x|) ≤
        C * (B0579.jb x ^ (-1 : ℝ) * |uψ x j|) := by
      intro j
      have hexp : B0579.jb x ^ (m / 2) =
          B0579.jb x ^ (-1 : ℝ) * B0579.jb x ^ ((m + 2) / 2) := by
        rw [B0579.jb_rpow_mul]; congr 1; ring
      calc B0579.jb x ^ (m / 2) * (|uψ x j| * |B0579.pd j (UnforcedLeray.B0238.Ec tr r) x|)
          = (B0579.jb x ^ (-1 : ℝ) * |uψ x j|) *
            (B0579.jb x ^ ((m + 2) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr r) x|) := by
            rw [hexp]; ring
        _ ≤ (B0579.jb x ^ (-1 : ℝ) * |uψ x j|) * C :=
            mul_le_mul_of_nonneg_left (hbd.2 j)
              (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (abs_nonneg _))
        _ = _ := by ring
    have h1 : ‖w r x‖ ≤ |uψ x 0| * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x| +
        |uψ x 1| * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x| := by
      simp only [hwdef]
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul]
    calc B0579.jb x ^ (m / 2) * ‖w r x‖
        ≤ B0579.jb x ^ (m / 2) * (|uψ x 0| * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x| +
          |uψ x 1| * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x|) :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = B0579.jb x ^ (m / 2) * (|uψ x 0| * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x|) +
          B0579.jb x ^ (m / 2) * (|uψ x 1| * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x|) := by
          ring
      _ ≤ C * (B0579.jb x ^ (-1 : ℝ) * |uψ x 0|) + C * (B0579.jb x ^ (-1 : ℝ) * |uψ x 1|) :=
          add_le_add (hj 0) (hj 1)
      _ = C * D x := by simp only [hDdef]; ring
  -- the uniform `X_m` bound
  set N : ℝ≥0∞ := eLpNorm (fun x => C * D x) 2 (volume.restrict (B0579.cell c)) with hN
  have hNtop : N < (⊤ : ℝ≥0∞) := (hD.const_mul C).2
  have hwn : ∀ r ∈ Icc (0 : ℝ) s, eLpNorm (w r) 2 (B0579.cellMeasure c m) ≤ N := by
    intro r hr
    rw [PairContAux.eLpNorm_cellMeasure_cx]
    refine eLpNorm_mono_ae ?_
    refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hw0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, Real.norm_eq_abs (C * D x)]
    exact (hwb r hr x hx).trans (le_abs_self _)
  have hwm : ∀ r ∈ Icc (0 : ℝ) s, MemLp (w r) 2 (B0579.cellMeasure c m) := fun r hr =>
    ⟨(hwaesm r hr.1).mono_ac (B0579.cellMeasure_ac c m), lt_of_le_of_lt (hwn r hr) hNtop⟩
  have hφm : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m)) := fun r hr => hA.memX r hr
  intro ρ hρ
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  have hIoo : ∀ r ∈ Ioo t s, r ∈ Icc (0 : ℝ) s ∧ r ∈ Icc t s := fun r hr =>
    ⟨⟨ht.trans hr.1.le, hr.2.le⟩, Ioo_subset_Icc_self hr⟩
  have hρI := hIoo ρ hρ
  -- the two terms
  set Aη : ℝ → ℂ := fun r => ∫ x in B0579.cell c, w r x * (φ r - φ ρ) x with hAη
  set Bη : ℝ → ℂ := fun r => ∫ x in B0579.cell c, w r x * φ ρ x with hBη
  have hsplit : ∀ r ∈ Ioo t s, (∫ x in B0579.cell c, φ r x * w r x) = Aη r + Bη r := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hIoo r hr
    have i1 := (PairContAux.holder (hwm r hr1) ((hφm r hr2).sub (hφm ρ hρI.2))).1
    have i2 := (PairContAux.holder (hwm r hr1) (hφm ρ hρI.2)).1
    rw [hAη, hBη]
    simp only
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- `A → 0`
  have hAt : Tendsto Aη (𝓝[Ioo t s] ρ) (𝓝 0) := by
    have hb : Tendsto (fun r => (xNorm c (-m) (φ r - φ ρ)).toReal) (𝓝[Icc t s] ρ) (𝓝 0) := by
      have h1 := hA.strongCont ρ hρI.2
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def] using this
    have hb' := (hb.mono_left (nhdsWithin_mono ρ Ioo_subset_Icc_self)).const_mul N.toReal
    rw [mul_zero] at hb'
    refine squeeze_zero_norm' ?_ hb'
    filter_upwards [self_mem_nhdsWithin] with r hr
    obtain ⟨hr1, hr2⟩ := hIoo r hr
    have h := (PairContAux.holder (hwm r hr1) ((hφm r hr2).sub (hφm ρ hρI.2))).2
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono hNtop.ne (hwn r hr1)
  -- `B` is continuous at `ρ`
  have hBc : ContinuousAt Bη ρ := by
    set bnd : ℝ × ℝ → ℝ := fun x =>
      ‖((B0579.jb x ^ (-m / 2) : ℝ) : ℂ) * φ ρ x‖ * (C * D x) with hbnd
    have hs1 : MemLp (fun x => ((B0579.jb x ^ (-m / 2) : ℝ) : ℂ) * φ ρ x) 2
        (volume.restrict (B0579.cell c)) := PairContAux.memLp_scaled (hφm ρ hρI.2)
    have hint : Integrable bnd (volume.restrict (B0579.cell c)) :=
      hs1.norm.integrable_mul (hD.const_mul C)
    have hφρ : Continuous (φ ρ) := (adjContDiff_slice hj (Ioo_subset_Ico_self hρ)).continuous
    refine continuousAt_of_dominated (bound := bnd) ?_ ?_ hint ?_
    · filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with r hr
      exact (hwaesm r (ht.trans hr.1.le)).mul hφρ.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with r hr
      refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hwr := hwb r (hIoo r hr).1 x hx
      have ha0 : 0 ≤ B0579.jb x ^ (-m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
      have hprod : B0579.jb x ^ (-m / 2) * B0579.jb x ^ (m / 2) = 1 := by
        rw [B0579.jb_rpow_mul]
        have : -m / 2 + m / 2 = 0 := by ring
        rw [this, Real.rpow_zero]
      rw [norm_mul, hbnd]
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
      calc ‖w r x‖ * ‖φ ρ x‖
          = (B0579.jb x ^ (-m / 2) * ‖φ ρ x‖) * (B0579.jb x ^ (m / 2) * ‖w r x‖) := by
            calc ‖w r x‖ * ‖φ ρ x‖
                = (B0579.jb x ^ (-m / 2) * B0579.jb x ^ (m / 2)) * (‖w r x‖ * ‖φ ρ x‖) := by
                  rw [hprod, one_mul]
              _ = _ := by ring
        _ ≤ (B0579.jb x ^ (-m / 2) * ‖φ ρ x‖) * (C * D x) :=
            mul_le_mul_of_nonneg_left hwr (mul_nonneg ha0 (norm_nonneg _))
    · refine Filter.Eventually.of_forall fun x => ?_
      have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
      have hE : ∀ j : Fin 2, ContinuousAt
          (fun r => B0579.pd j (UnforcedLeray.B0238.Ec tr r) x) ρ := by
        intro j
        have h1 := (GlobEAux.contOn_pd_Ec tr j).continuousAt
          (hU.mem_nhds (show ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from
            ⟨hρ0, mem_univ _⟩))
        exact h1.comp (f := fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ)))
          (continuous_id.prodMk continuous_const).continuousAt
      have hr : ContinuousAt (fun r => uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
          uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x) ρ :=
        (continuousAt_const.mul (hE 0)).add (continuousAt_const.mul (hE 1))
      exact (Complex.continuous_ofReal.continuousAt.comp hr).mul continuousAt_const
  -- conclusion
  have hAρ : Aη ρ = 0 := by simp [hAη]
  have hGρ : (∫ x in B0579.cell c, φ ρ x * w ρ x) = Bη ρ := by
    rw [hsplit ρ hρ, hAρ, zero_add]
  have hT : Tendsto (fun r => Aη r + Bη r) (𝓝[Ioo t s] ρ) (𝓝 (Bη ρ)) := by
    have := hAt.add (hBc.continuousWithinAt (s := Ioo t s)).tendsto
    simpa using this
  show Tendsto (fun r => ∫ x in B0579.cell c, φ r x * w r x) (𝓝[Ioo t s] ρ)
    (𝓝 (∫ x in B0579.cell c, φ ρ x * w ρ x))
  rw [hGρ]
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hsplit r hr).symm

end UnforcedLeray.Short.IIIa
