import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1

/-!
# Completeness of `𝓗` (`PartIII-a:T18/2/1/2`; SP 3427-3440)

Proves `CausalCompleteH` (`Sub/T18_2_1.lean`, line 53), with source
`the November 2 reference manuscript`, lines 3427-3440.

Route A. The shifted differences `v k = g⁻¹ • (bn (k + N₁) - bn N₁)` (`g = gainG > 0`) form a
Cauchy sequence in `L²(ageμ c (-3/2); EuclideanSpace ℂ (Fin 2))`, which is complete. The limit
has a strongly measurable representative `D`; put `b = bn N₁ + g · D`. Since `g` is a positive
real scalar, `gainConj γ ν (bn n - b) = v (n - N₁) - D` pointwise.
The hypotheses `0 < c`, `0 < ν` are not used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Elementary identities -/

lemma ch_norm_toLp (x : Fin 2 → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ = vnorm2 x := by
  rw [EuclideanSpace.norm_eq]
  simp [vnorm2]

lemma ch_norm_toLp_sub (x y : Fin 2 → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2)) - WithLp.toLp 2 y‖ = vnorm2 (x - y) := by
  have h : (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2)) - WithLp.toLp 2 y
      = WithLp.toLp 2 (x - y) := by
    ext i
    simp
  rw [h, ch_norm_toLp]

lemma ch_norm_toLp_sub_ofLp (x : Fin 2 → ℂ) (y : EuclideanSpace ℂ (Fin 2)) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2)) - y‖ = vnorm2 (x - WithLp.ofLp y) := by
  have h := ch_norm_toLp_sub x (WithLp.ofLp y)
  rwa [WithLp.toLp_ofLp] at h

lemma ch_gainConj_coord (γ ν : ℝ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ))
    (i : Fin 2) :
    gainConj γ ν f p i = (((gainG γ ν p.1)⁻¹ : ℝ) : ℂ) * f p i := by
  simp only [gainConj, Pi.smul_apply, Complex.real_smul]

lemma ch_coord_identity (g : ℝ) (hg : g ≠ 0) (x y z : ℂ) :
    ((g⁻¹ : ℝ) : ℂ) * (x - y) - z = ((g⁻¹ : ℝ) : ℂ) * (x - (y + (g : ℂ) * z)) := by
  have hinv : ((g⁻¹ : ℝ) : ℂ) * (g : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hg, Complex.ofReal_one]
  linear_combination z * hinv

lemma ch_measurable_gainG (γ ν : ℝ) : Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 := by
  have h : Measurable fun s : ℝ => gainG γ ν s := by
    unfold gainG
    first
      | fun_prop
      | exact Real.continuous_exp.measurable.comp
          ((measurable_const.mul measurable_id).div
            (measurable_const.add (measurable_const.mul measurable_id)))
  exact h.comp measurable_fst

/-! ## Completeness of `L²` for the shifted sequence (abstract measure) -/

theorem ch_l2_limit (μ : Measure (ℝ × (ℝ × ℝ))) (v : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (hfin : ∀ k, MemLp (fun p => (WithLp.toLp 2 (v k p) : EuclideanSpace ℂ (Fin 2))) 2 μ)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) (a : ℕ → ℝ≥0∞) (ha : Tendsto a atTop (𝓝 0))
    (hcau : ∀ k l, eLpNorm (fun p => vnorm2 (v k p - v l p)) 2 μ ≤ K * (a k + a l)) :
    ∃ d : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => d p i) ∧
      Tendsto (fun k => eLpNorm (fun p => vnorm2 (v k p - d p)) 2 μ) atTop (𝓝 0) := by
  have hedist_eq : ∀ k l, edist ((hfin k).toLp _) ((hfin l).toLp _)
      = eLpNorm (fun p => vnorm2 (v k p - v l p)) 2 μ := by
    intro k l
    have hfun : (fun p => vnorm2 (v k p - v l p)) = fun p =>
        ‖((fun p => (WithLp.toLp 2 (v k p) : EuclideanSpace ℂ (Fin 2))) -
          (fun p => (WithLp.toLp 2 (v l p) : EuclideanSpace ℂ (Fin 2)))) p‖ := by
      funext p
      exact (ch_norm_toLp_sub _ _).symm
    rw [Lp.edist_toLp_toLp, hfun, eLpNorm_norm]
  have hT : Tendsto (fun q : ℕ × ℕ => edist ((hfin q.1).toLp _) ((hfin q.2).toLp _))
      atTop (𝓝 0) := by
    have hfst : Tendsto (fun q : ℕ × ℕ => q.1) atTop atTop :=
      Filter.tendsto_atTop_atTop.2 (fun b => ⟨(b, 0), fun x hx => hx.1⟩)
    have hsnd : Tendsto (fun q : ℕ × ℕ => q.2) atTop atTop :=
      Filter.tendsto_atTop_atTop.2 (fun b => ⟨(0, b), fun x hx => hx.2⟩)
    have h0 : Tendsto (fun q : ℕ × ℕ => K * (a q.1 + a q.2)) atTop (𝓝 (K * (0 + 0))) :=
      ENNReal.Tendsto.const_mul ((ha.comp hfst).add (ha.comp hsnd)) (Or.inr hK)
    rw [add_zero, mul_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
      (fun q => (hedist_eq q.1 q.2).le.trans (hcau q.1 q.2))
  have hcs : CauchySeq (fun k => (hfin k).toLp _) := by
    rw [EMetric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hT.eventually (gt_mem_nhds hε))
    exact ⟨max N.1 N.2, fun n hn => hN (n, max N.1 N.2)
      (show N.1 ≤ n ∧ N.2 ≤ max N.1 N.2 from
        ⟨le_trans (le_max_left _ _) hn, le_max_right _ _⟩)⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLm := Lp.aestronglyMeasurable L
  obtain ⟨D, hDm, hLD⟩ : ∃ D : ℝ × (ℝ × ℝ) → EuclideanSpace ℂ (Fin 2),
      StronglyMeasurable D ∧ (⇑L) =ᵐ[μ] D :=
    ⟨hLm.mk _, hLm.stronglyMeasurable_mk, hLm.ae_eq_mk⟩
  refine ⟨fun p => WithLp.ofLp (D p), fun i => ?_, ?_⟩
  · have hc : Continuous fun f : EuclideanSpace ℂ (Fin 2) => WithLp.ofLp f i := by
      fun_prop
    exact (hc.comp_stronglyMeasurable hDm).measurable
  · have hk : ∀ k, edist ((hfin k).toLp _) L
        = eLpNorm (fun p => vnorm2 (v k p - WithLp.ofLp (D p))) 2 μ := by
      intro k
      calc edist ((hfin k).toLp _) L
          = eLpNorm (⇑((hfin k).toLp _) - ⇑L) 2 μ := Lp.edist_def _ _
        _ = eLpNorm ((fun p => (WithLp.toLp 2 (v k p) : EuclideanSpace ℂ (Fin 2))) - D) 2 μ := by
            apply eLpNorm_congr_ae
            filter_upwards [(hfin k).coeFn_toLp, hLD] with p h1 h2
            simp only [Pi.sub_apply, h1, h2]
        _ = eLpNorm (fun p => ‖(WithLp.toLp 2 (v k p) : EuclideanSpace ℂ (Fin 2)) - D p‖) 2 μ :=
            (eLpNorm_norm _).symm
        _ = eLpNorm (fun p => vnorm2 (v k p - WithLp.ofLp (D p))) 2 μ := by
            congr 1
            funext p
            exact ch_norm_toLp_sub_ofLp _ _
    exact Filter.Tendsto.congr hk (tendsto_iff_edist_tendsto_0.1 hL)

/-! ## Completeness of `𝓗` -/

theorem causalCompleteH : CausalCompleteH := by
  unfold CausalCompleteH
  intro c ν γ _hc _hν bn hbn K a hK ha hcau
  obtain ⟨N0, hN0⟩ := hcau
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 ha 1 zero_lt_one)
  obtain ⟨N1, hN1a, hN1b⟩ : ∃ N1 : ℕ, N0 ≤ N1 ∧ N2 ≤ N1 :=
    ⟨max N0 N2, le_max_left _ _, le_max_right _ _⟩
  have ha1 : ∀ n, N1 ≤ n → a n ≠ ⊤ := fun n hn =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hN2 n (le_trans hN1b hn))
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 := ch_measurable_gainG γ ν
  have hg0 : ∀ q : ℝ × (ℝ × ℝ), gainG γ ν q.1 ≠ 0 := fun q => (Real.exp_pos _).ne'
  have hcont : Continuous (WithLp.toLp 2 : (Fin 2 → ℂ) → EuclideanSpace ℂ (Fin 2)) := by
    fun_prop
  -- membership in L² of the shifted sequence
  have hmemv : ∀ k : ℕ, MemLp (fun p => (WithLp.toLp 2
      (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p) : EuclideanSpace ℂ (Fin 2)))
      2 (ageμ c (-3 / 2)) := by
    intro k
    have hcomp : Measurable fun p => gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p := by
      apply measurable_pi_iff.2
      intro i
      simp only [ch_gainConj_coord]
      exact (Complex.measurable_ofReal.comp hg.inv).mul
        ((hbn (k + N1) i).sub (hbn N1 i))
    unfold MemLp
    refine ⟨hcont.comp_aestronglyMeasurable hcomp.aestronglyMeasurable, ?_⟩
    have hfun : (fun p => vnorm2 (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p))
        = fun p => ‖(WithLp.toLp 2 (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p) :
            EuclideanSpace ℂ (Fin 2))‖ := by
      funext p
      exact (ch_norm_toLp _).symm
    have h2 : eLpNorm (fun p => (WithLp.toLp 2
        (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p) : EuclideanSpace ℂ (Fin 2)))
        2 (ageμ c (-3 / 2))
        = hCalNorm c (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i)) := by
      unfold hCalNorm
      rw [hfun, eLpNorm_norm]
    rw [h2]
    exact lt_of_le_of_lt (hN0 (k + N1) N1 (by omega) hN1a)
      (ENNReal.mul_lt_top hK.lt_top (ENNReal.add_lt_top.2
        ⟨(ha1 (k + N1) (by omega)).lt_top, (ha1 N1 le_rfl).lt_top⟩))
  -- the shifted differences are Cauchy with the hypothesised bound
  have hcau' : ∀ k l : ℕ,
      eLpNorm (fun p => vnorm2 (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p
        - gainConj γ ν (fun p i => bn (l + N1) p i - bn N1 p i) p)) 2 (ageμ c (-3 / 2))
        ≤ K * (a (k + N1) + a (l + N1)) := by
    intro k l
    have hdiff : ∀ p : ℝ × (ℝ × ℝ),
        gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p
          - gainConj γ ν (fun p i => bn (l + N1) p i - bn N1 p i) p
        = gainConj γ ν (fun p i => bn (k + N1) p i - bn (l + N1) p i) p := by
      intro p
      funext i
      simp only [Pi.sub_apply, ch_gainConj_coord]
      ring
    have h := hN0 (k + N1) (l + N1) (by omega) (by omega)
    refine le_trans (le_of_eq ?_) h
    unfold hCalNorm
    congr 1
    funext p
    rw [hdiff p]
  obtain ⟨d, hd, hlim⟩ := ch_l2_limit (ageμ c (-3 / 2))
    (fun k => gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i))
    hmemv K hK (fun k => a (k + N1)) (ha.comp (tendsto_add_atTop_nat N1)) hcau'
  -- pointwise identity: the difference with the candidate limit `b`
  have hpt : ∀ k : ℕ,
      eLpNorm (fun p => vnorm2 (gainConj γ ν (fun p i => bn (k + N1) p i - bn N1 p i) p
          - d p)) 2 (ageμ c (-3 / 2))
        = hCalNorm c (gainConj γ ν (fun p i => bn (k + N1) p i
            - (bn N1 p i + ((gainG γ ν p.1 : ℝ) : ℂ) * d p i))) := by
    intro k
    unfold hCalNorm
    congr 1
    funext p
    congr 1
    funext i
    simp only [Pi.sub_apply, ch_gainConj_coord]
    exact ch_coord_identity _ (hg0 p) _ _ _
  refine ⟨fun p i => bn N1 p i + ((gainG γ ν p.1 : ℝ) : ℂ) * d p i, fun i => ?_, ?_⟩
  · exact (hbn N1 i).add ((Complex.measurable_ofReal.comp hg).mul (hd i))
  · rw [← Filter.tendsto_add_atTop_iff_nat N1]
    exact Filter.Tendsto.congr (fun k => hpt k) hlim

end UnforcedLeray.Short.IIIa
