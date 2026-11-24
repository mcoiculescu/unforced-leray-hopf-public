import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Lib.BudgetsGronwall.VariationOfConstants

/-!
# Part I, task `PartI:T02/3` (uniqueness leaf): `ClassicalUniquenessBounded`

Target: `classicalUniquenessBounded_of (hC : ClassicalCutoffEnergyIneq) : ClassicalUniquenessBounded`,
with the statements of `Short/PartI/Sub/T02_3.lean` taken as given.

Source of record: `the November 2 reference manuscript`, lines 276-288
(uniqueness among bounded classical solutions with the same datum).

Proof outline, for two classical solutions `v`, `v'` with the same bounds `M`, an age `s ∈ [0,T]`
and the cutoff energy `F_R(r) = ∫_cell φ_R(η) |v(r) - v'(r)|²`:

1. `ClassicalCutoffEnergyIneq` gives one constant `C ≥ 0` (independent of `R`) with
   `F_R(r) ≤ C ∫₀ʳ F_R + C/√R` on `[0,T]`.
2. The integral Gronwall lemma `UnforcedLeray.Gronwall.le_exp_of_integral_le` yields
   `F_R(s) ≤ (C/√R) e^{sC}` for `R ≥ 1`.
3. `etaCutoff R η → 1` as `R → ∞`, with `0 ≤ etaCutoff ≤ 1`. Dominated convergence (bound `|w|²`,
   integrable on the cell by `finite_energy`) gives `F_R(s) → ∫_cell |w(s)|²`, `w = v - v'`.
4. Hence `0 ≤ ∫_cell |w(s)|² ≤ lim (C/√R) e^{sC} = 0`.
5. `w(s)` is continuous, `c`-periodic in `q`, and has vanishing cell energy, so `w(s) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Elementary inequality -/

/-- `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem cuSqNormSubLeTwo (a b : Vec) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-! ### Facts about the transverse cutoff `etaCutoff` (`Short/PartI/Sub/T05.lean`) -/

/-- The cutoff takes values in `[0,1]`. -/
theorem cuEtaCutoffUnit (R η : ℝ) : 0 ≤ etaCutoff R η ∧ etaCutoff R η ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2 - |η| / R)
  have h1 := Real.smoothTransition.le_one (2 - |η| / R)
  unfold etaCutoff
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- For fixed `η`, the cutoff tends to `1` as `R → ∞`. -/
theorem cuEtaCutoffTendsto (η : ℝ) : Tendsto (fun R : ℝ => etaCutoff R η) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max 1 |η|)] with R hR
  show (1 : ℝ) = etaCutoff R η
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRa : |η| ≤ R := le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := by linarith
  have hdiv : |η| / R ≤ 1 := (div_le_one₀ hRpos).2 hRa
  have hsm : Real.smoothTransition (2 - |η| / R) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold etaCutoff
  rw [hsm]
  norm_num

/-- The map `z ↦ etaCutoff R z.2` is continuous on the plane. -/
theorem cuEtaCutoffContinuous (R : ℝ) : Continuous (fun z : Plane => etaCutoff R z.2) := by
  unfold etaCutoff
  have h1 : Continuous (fun z : Plane => 2 - |z.2| / R) := by fun_prop
  exact (Real.smoothTransition.continuous.comp h1).pow 2

/-! ### Continuity of a classical velocity at a fixed age -/

/-- The velocity of a classical solution is continuous in space at every age `s ∈ [0,T]`. -/
theorem cuVelocityContinuous {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcl : IsClassicalOn ν c T v p) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Continuous (fun z : Plane => v s z) := by
  have h1 : ContinuousOn (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ) :=
    hcl.smooth_v.continuousOn
  have h2 : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    continuous_const.prodMk continuous_id
  exact h1.comp_continuous h2 (fun z => mk_mem_prod hs (mem_univ z))

/-! ### Pure measure theory: a continuous periodic field with vanishing cell energy is zero -/

/-- A continuous, `c`-periodic-in-`q` vector field with integrable squared norm on the cell and
vanishing cell energy vanishes identically. -/
theorem cuEqZeroOfCellEnergyZero {c : ℝ} (hc : 0 < c) {w : Plane → Vec} (hw : Continuous w)
    (hper : ∀ η : ℝ, Function.Periodic (fun q : ℝ => w (q, η)) c)
    (hi : Integrable (fun z => ‖w z‖ ^ 2) (volume.restrict (Cyl.cell c)))
    (hint : ∫ z in Cyl.cell c, ‖w z‖ ^ 2 = 0) : ∀ z : Plane, w z = 0 := by
  have hcont : Continuous (fun z => ‖w z‖ ^ 2) := hw.norm.pow 2
  have hnn : (0 : Plane → ℝ) ≤ fun z => ‖w z‖ ^ 2 :=
    Pi.le_def.2 (fun z => sq_nonneg _)
  -- (a) `g = 0` a.e. on the cell
  have hae : (fun z => ‖w z‖ ^ 2) =ᵐ[volume.restrict (Cyl.cell c)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hi).1 hint
  -- (b) `g = 0` a.e. on the open strip `U`, hence pointwise on `U` by continuity
  have hUcell : Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) ⊆ Cyl.cell c := by
    unfold Cyl.cell
    exact prod_mono Ioo_subset_Ico_self (subset_refl _)
  have hUae : (fun z => ‖w z‖ ^ 2) =ᵐ[volume.restrict (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))] 0 :=
    ae_restrict_of_ae_restrict_of_subset hUcell hae
  have hUopen : IsOpen (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hU0 : EqOn (fun z => ‖w z‖ ^ 2) 0 (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) :=
    Measure.eqOn_open_of_ae_eq hUae hUopen hcont.continuousOn continuous_zero.continuousOn
  -- (c) `g = 0` on the closed strip `K = closure U`
  have hab : -c / 2 < c / 2 := by linarith
  have hclosure : closure (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))
      = Icc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
  have hK0 : EqOn (fun z => ‖w z‖ ^ 2) 0 (Icc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) :=
    Set.EqOn.of_subset_closure hU0 hcont.continuousOn continuous_zero.continuousOn
      (prod_mono Ioo_subset_Icc_self (subset_refl _)) hclosure.symm.subset
  -- (d) every point is a `q`-translate of a point of the closed strip, and `w` is invariant
  intro z
  have hfl1 : ((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) * c ≤ z.1 + c / 2 :=
    (le_div_iff₀ hc).1 (Int.floor_le _)
  have hfl2 : z.1 + c / 2 < (((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1) * c :=
    (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
  generalize ⌊(z.1 + c / 2) / c⌋ = m at hfl1 hfl2
  have hmem : (z.1 - (m : ℝ) * c, z.2) ∈ Icc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := by
    refine mk_mem_prod ⟨?_, ?_⟩ (mem_univ _)
    · linarith
    · have hm : ((m : ℝ) + 1) * c = (m : ℝ) * c + c := by ring
      linarith
  have hz' : ‖w (z.1 - (m : ℝ) * c, z.2)‖ ^ 2 = 0 := hK0 hmem
  have hperz : w (z.1 - (m : ℝ) * c, z.2) = w (z.1, z.2) :=
    (hper z.2).sub_int_mul_eq m
  have hnorm : ‖w (z.1, z.2)‖ ^ 2 = 0 := by
    rw [← hperz]
    exact hz'
  have hnorm' : ‖w (z.1, z.2)‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 hnorm
  exact norm_eq_zero.1 hnorm'

/-! ### The target -/

/-- **`ClassicalUniquenessBounded` from the cutoff energy inequality.** Two bounded classical
solutions with the same datum agree on `[0,T]`: the cutoff energy of the difference is controlled
by Gronwall with the `R`-decaying source `C/√R`, hence its cell energy vanishes, hence the
difference is zero. -/
theorem classicalUniquenessBounded_of (hC : ClassicalCutoffEnergyIneq) :
    ClassicalUniquenessBounded := by
  intro ν c T M v v' p p' hν hc hT hcl hcl' hb hb' hB hB' s hs
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC0, hCb⟩ := hC ν c T M v v' p p' hν hc hT hcl hcl' hb hb' hB hB'
  have hsT : s ≤ T := hs.2
  -- Gronwall: `F_R(s) ≤ (C/√R) e^{sC}` for `R ≥ 1`.
  have key : ∀ R : ℝ, 1 ≤ R →
      classicalCutoffEnergy c v v' R s ≤ C / Real.sqrt R * Real.exp (s * C) := by
    intro R hR
    obtain ⟨hcont, hineq⟩ := hCb R hR
    have hG : ∀ t ∈ Icc (0 : ℝ) s, classicalCutoffEnergy c v v' R t ≤
        C / Real.sqrt R + ∫ r in (0 : ℝ)..t, C * classicalCutoffEnergy c v v' R r := by
      intro t ht
      rw [intervalIntegral.integral_const_mul]
      have h := hineq t ⟨ht.1, ht.2.trans hsT⟩
      linarith
    have hle := UnforcedLeray.Gronwall.le_exp_of_integral_le
      (y := classicalCutoffEnergy c v v' R) (β := fun _ => C) (A := C / Real.sqrt R)
      (s := 0) (T := s) (hcont.mono (Icc_subset_Icc le_rfl hsT)) continuousOn_const
      (fun _ _ => hC0) hG s ⟨hs.1, le_rfl⟩
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using hle
  -- Continuity and integrability of the difference at age `s`.
  have hvc : Continuous (fun z : Plane => v s z) := cuVelocityContinuous hcl hs
  have hvc' : Continuous (fun z : Plane => v' s z) := cuVelocityContinuous hcl' hs
  have hw : Continuous (fun z : Plane => v s z - v' s z) := hvc.sub hvc'
  have hdiff_cont : Continuous (fun z : Plane => ‖v s z - v' s z‖ ^ 2) := hw.norm.pow 2
  have hi : Integrable (fun z : Plane => ‖v s z - v' s z‖ ^ 2) (volume.restrict (Cyl.cell c)) := by
    have h1 : Integrable (fun z : Plane => ‖v s z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
      hcl.finite_energy s hs
    have h2 : Integrable (fun z : Plane => ‖v' s z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
      hcl'.finite_energy s hs
    refine Integrable.mono' ((h1.const_mul 2).add (h2.const_mul 2))
      hdiff_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    show ‖‖v s z - v' s z‖ ^ 2‖ ≤ 2 * ‖v s z‖ ^ 2 + 2 * ‖v' s z‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact cuSqNormSubLeTwo _ _
  -- Uniform domination of the cutoff integrand by the difference.
  have hbd : ∀ R : ℝ, ∀ z : Plane,
      ‖etaCutoff R z.2 * ‖v s z - v' s z‖ ^ 2‖ ≤ ‖v s z - v' s z‖ ^ 2 := by
    intro R z
    obtain ⟨h0, h1⟩ := cuEtaCutoffUnit R z.2
    have hq : 0 ≤ ‖v s z - v' s z‖ ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg h0 hq)]
    nlinarith
  -- Pointwise limit of the integrand as `R → ∞`.
  have hpt : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)),
      Tendsto (fun R : ℝ => etaCutoff R z.2 * ‖v s z - v' s z‖ ^ 2) atTop
        (𝓝 (‖v s z - v' s z‖ ^ 2)) := by
    refine ae_of_all _ fun z => ?_
    have h := (cuEtaCutoffTendsto z.2).mul_const (‖v s z - v' s z‖ ^ 2)
    rwa [one_mul] at h
  -- Dominated convergence: the cutoff energy converges to the cell energy of the difference.
  have hlim : Tendsto (fun R : ℝ => ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖v s z - v' s z‖ ^ 2)
      atTop (𝓝 (∫ z in Cyl.cell c, ‖v s z - v' s z‖ ^ 2)) :=
    tendsto_integral_filter_of_dominated_convergence (fun z => ‖v s z - v' s z‖ ^ 2)
      (Eventually.of_forall fun R => ((cuEtaCutoffContinuous R).mul hdiff_cont).aestronglyMeasurable)
      (Eventually.of_forall fun R => ae_of_all _ fun z => hbd R z) hi hpt
  have hlim' : Tendsto (fun R : ℝ => classicalCutoffEnergy c v v' R s) atTop
      (𝓝 (∫ z in Cyl.cell c, ‖v s z - v' s z‖ ^ 2)) := hlim
  -- The Gronwall bound tends to zero.
  have hg : Tendsto (fun R : ℝ => C / Real.sqrt R * Real.exp (s * C)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => C / Real.sqrt R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have h2 := h1.mul_const (Real.exp (s * C))
    rwa [zero_mul] at h2
  have hev : ∀ᶠ R in atTop,
      classicalCutoffEnergy c v v' R s ≤ C / Real.sqrt R * Real.exp (s * C) :=
    (eventually_ge_atTop (1 : ℝ)).mono fun R hR => key R hR
  have hle : ∫ z in Cyl.cell c, ‖v s z - v' s z‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hlim' hg hev
  have hnonneg : 0 ≤ ∫ z in Cyl.cell c, ‖v s z - v' s z‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun z => sq_nonneg _
  have hint0 : ∫ z in Cyl.cell c, ‖v s z - v' s z‖ ^ 2 = 0 := le_antisymm hle hnonneg
  -- The difference is continuous, `c`-periodic in `q`, and has vanishing cell energy.
  have hper : ∀ η : ℝ,
      Function.Periodic (fun q : ℝ => (fun z : Plane => v s z - v' s z) (q, η)) c := by
    intro η q
    have e1 : v s (q + c, η) = v s (q, η) := hcl.periodic_v s hs (q, η)
    have e2 : v' s (q + c, η) = v' s (q, η) := hcl'.periodic_v s hs (q, η)
    show v s (q + c, η) - v' s (q + c, η) = v s (q, η) - v' s (q, η)
    rw [e1, e2]
  have hw0 := cuEqZeroOfCellEnergyZero hc0 hw hper hi hint0
  funext z
  exact sub_eq_zero.1 (hw0 z)

end UnforcedLeray.Short.PartI
