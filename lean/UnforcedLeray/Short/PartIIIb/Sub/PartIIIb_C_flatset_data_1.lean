import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves

/-!


Source `the November 2 reference manuscript`
lines 4562-4570 (`V_G`, `E_s = curl V_G`, `H_{s,c}`, `R_{s,c}`; "the vorticity sources are centrally
even and have zero circulation"), 4565 (`a(t) = 1 + νt`).

The Gaussian profiles `hMode a`, `rMode a` (`a = srcA ν s ≥ 1`) are bounded by
`C (1+|x|²)² e^{-|x|²/(4a)}` and measurable, hence integrable on the plane, with zero plane integral;
their periodizations lie in `L²(cell, ⟨x⟩^{2m})`, have zero circulation (the cell integral of the
periodization is the plane integral), are centrally even, and depend continuously on `s` in `L²`.
The Props below are these leaves; `gaussSourcesExist_of` assembles them.  The Props
`PeriodizeL2Bound` and `GaussPointBound` are shared with `FlatSrcBdd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Gaussian pointwise bound of the source profiles** (source 4565-4570, `gaussE`, `gaussRdE`):
for `1 ≤ a ≤ A`, `|hMode a x|, |rMode a x| ≤ C (1+|x|²)² e^{-|x|²/(4A)}`, `C` depending on `A` only.
Route: `‖angTwo x‖ ≤ 1`; `gaussE a r = a⁻²(2 - r²/(2a))e^{-r²/(4a)}`, `gaussRdE a r = r·deriv (gaussE a) r
= -a⁻²(r²/(2a))(4 - r²/(2a))e^{-r²/(4a)}` (`deriv` of the closed form; `gaussRdE a 0 = 0`), `a ≥ 1`,
`e^{-r²/(4a)} ≤ e^{-r²/(4A)}` for `a ≤ A`. -/
def GaussPointBound : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
    ‖hMode a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) ∧
    ‖rMode a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A))

/-- The source profiles are measurable (`gaussRdE` involves `deriv`: `measurable_deriv`;
`IIIa.angTwo` is a quotient of continuous functions). -/
def GaussMeasurable : Prop := ∀ a : ℝ, Measurable (hMode a) ∧ Measurable (rMode a)

/-- **Weighted `L²` bound of the periodization of a Gaussian-bounded function, uniformly in the
period `c ≥ c₀`** (source 4562-4570, 4565-4574: "the periodic images are at distance `≥ c/2` from the
cell").  Route in two steps.  (i) pointwise on the cell `|x₁| ≤ c/2`:
`‖periodizeC c g x‖ ≤ C K e^{-(x₁²+x₂²)/(16A)}`: with `u_n = x₁ - nc`, `(1+r²)²e^{-r²/(4A)} ≤ M e^{-r²/(8A)}`,
`u_n² ≥ x₁²` and `u_n² ≥ n²c²/4` for `n ≠ 0`, so the lattice sum is
`≤ M e^{-x₁²/(16A)}e^{-x₂²/(8A)}(1 + 2Σ_{n≥1}e^{-n²c₀²/(64A)})`.  (ii) a function `h` with
`‖h x‖ ≤ B e^{-|x|²/(16A)}` on the cell has `eLpNorm h 2 (cellMeasure c m) ≤ C' B`, `C'` independent
of `c`: `cellMeasure c m = (volume.restrict (cell c)).withDensity (density m)`, weight
`(1+x₁²+x₂²)^m`, and `∫_ℝ² (1+|x|²)^m e^{-|x|²/(8A)} < ∞`.  Measurability: `periodizeC` of a measurable
`g` with the Gaussian bound is measurable (summable pointwise). -/
def PeriodizeL2Bound : Prop :=
  ∀ (m A c₀ : ℝ), 0 < A → 0 < c₀ → ∃ C : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ (g : ℝ × ℝ → ℂ) (K : ℝ),
    Measurable g →
    (∀ x : ℝ × ℝ, ‖g x‖ ≤
      K * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A))) →
    AEStronglyMeasurable (IIIa.periodizeC c g) (B0579.cellMeasure c m) ∧
    eLpNorm (IIIa.periodizeC c g) 2 (B0579.cellMeasure c m) ≤ ENNReal.ofReal (C * K)

/-- **Pointwise Gaussian bound of the periodization on the cell, uniformly in `c ≥ c₀`**
(source 4565-4574: the images are at distance `≥ c/2`).  For `|x₁| ≤ c/2`:
`‖periodizeC c g x‖ ≤ C K e^{-(x₁²+x₂²)/(16A)}`.  Route: with `u_n = x₁ - nc`, `(1+r²)²e^{-r²/(4A)} ≤
M e^{-r²/(8A)}` (`M` depends on `A`), `u_0² = x₁²`, `u_n² ≥ x₁²` and `u_n² ≥ n²c²/4 ≥ n²c₀²/4` for `n ≠ 0`
(`|x₁| ≤ c/2 ≤ |n|c/2`), so `e^{-u_n²/(8A)} ≤ e^{-x₁²/(16A)}e^{-n²c₀²/(64A)}`; sum over `n ∈ ℤ`
(`summable_exp_neg_mul_sq`-type, e.g. `Summable (fun n : ℤ => exp (-b n²))`), `norm_tsum_le_tsum_norm`. -/
def PeriodizePointBound : Prop :=
  ∀ (A c₀ : ℝ), 0 < A → 0 < c₀ → ∃ C : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ (g : ℝ × ℝ → ℂ) (K : ℝ),
    (∀ x : ℝ × ℝ, ‖g x‖ ≤
      K * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A))) →
    ∀ x : ℝ × ℝ, |x.1| ≤ c / 2 →
      ‖IIIa.periodizeC c g x‖ ≤ C * K * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))

/-- **Weighted `L²` norm of a Gaussian on the cell, uniformly in `c`** (source 4562, 2828:
`X_{m,c} = L²(C_c, ⟨x⟩^{2m}dx)`): if `‖h x‖ ≤ B e^{-|x|²/(16A)}` for `|x₁| ≤ c/2` then
`‖h‖_{L²(cellMeasure c m)} ≤ C B` with `C = C(m, A)` independent of `c`.  Route: `cellMeasure c m =
(volume.restrict (cell c)).withDensity (density m)`, `density m x = (1+x₁²+x₂²)^m`,
`eLpNorm_le_of_ae_bound`-style or `lintegral_withDensity_eq_lintegral_mul`, then
`∫_{ℝ²}(1+|x|²)^m e^{-|x|²/(8A)} dx < ∞` (e.g. bound `(1+|x|²)^m ≤ M e^{|x|²/(16A)}`, product of 1-D
Gaussians `integral_gaussian`), constant independent of `c` since the cell is inside `ℝ²`. -/
def WeightedL2Gauss : Prop :=
  ∀ (m A : ℝ), 0 < A → ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∀ (h : ℝ × ℝ → ℂ) (B : ℝ),
    AEStronglyMeasurable h (B0579.cellMeasure c m) →
    (∀ x : ℝ × ℝ, |x.1| ≤ c / 2 → ‖h x‖ ≤ B * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) →
    eLpNorm h 2 (B0579.cellMeasure c m) ≤ ENNReal.ofReal (C * B)

/-- **Measurability of a periodization of a Gaussian-bounded measurable function** (source 4568):
for `c > 0` the lattice sum converges pointwise (Gaussian bound), `periodizeC c g` is the limit of
the finite partial sums over `|n| ≤ N` (`HasSum.tendsto_sum_nat`-type, e.g.
`measurable_of_tendsto_metrizable`), each measurable. -/
def PeriodizeMeas : Prop :=
  ∀ (c A K : ℝ) (g : ℝ × ℝ → ℂ), 0 < c → 0 < A → Measurable g →
    (∀ x : ℝ × ℝ, ‖g x‖ ≤
      K * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A))) →
    Measurable (IIIa.periodizeC c g)

theorem periodizeL2Bound_of (hp : PeriodizePointBound) (hw : WeightedL2Gauss)
    (hm : PeriodizeMeas) : PeriodizeL2Bound := by
  intro m A c₀ hA hc₀
  obtain ⟨Cp, hCp⟩ := hp A c₀ hA hc₀
  obtain ⟨Cw, hCw⟩ := hw m A hA
  refine ⟨Cw * Cp, fun c hc g K hg hb => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le hc₀ hc
  have hmeas := (hm c A K g hc0 hA hg hb).aestronglyMeasurable (μ := B0579.cellMeasure c m)
  refine ⟨hmeas, ?_⟩
  have := hCw c hc0 (IIIa.periodizeC c g) (Cp * K) hmeas (fun x hx => hCp c hc g K hb x hx)
  rwa [← mul_assoc] at this

/-- **The circulation of a periodization is the plane integral** (source 4562-4570: "zero
circulation", `∫_cell P_c g = ∫_{ℝ²} g`).  Route: `∫_cell F = ∫_{|q| ≤ c/2}∫_ℝ F(q,η) dη dq`
(`Cyl.integral_cell_eq_integral_integral`), `∑'` and `∫` commute by integrability (`integral_tsum` or
`hasSum_integral_of_summable_norm`), `∫_{|q| ≤ c/2} g(q - nc, η) = ∫_{(n-1/2)c ≤ q ≤ (n+1/2)c} g`, and the
intervals tile `ℝ` up to null sets (`MeasureTheory.integral_iUnion_ae` or the `ℤ`-translate sum). -/
def PeriodizeIntegral : Prop :=
  ∀ (c : ℝ) (g : ℝ × ℝ → ℂ), 0 < c → Integrable g →
    ∫ x in B0579.cell c, IIIa.periodizeC c g x = ∫ x, g x

/-- The source profiles are integrable on the plane (source 4565-4570; bound `GaussPointBound`,
`∫ (1+|x|²)²e^{-|x|²/(4A)} < ∞` in polar or product form, `Integrable.mono'`). -/
def PlaneIntegrable : Prop :=
  ∀ a : ℝ, 1 ≤ a → Integrable (hMode a) ∧ Integrable (rMode a)

/-- **Zero plane integrals of the source profiles** (source 4569-4570: "zero circulation"):
`∫_{ℝ²} rE'(r)e^{2iϑ} = 0` (angular integral of `e^{2iϑ}`, i.e. `∫₀^{2π} e^{2iϑ} dϑ = 0`, polar
coordinates `integral_comp_polarCoord_symm`) and `∫_{ℝ²}(rE' + 2E) = 2π∫₀^∞(rE'+2E) r dr
= 2π [r²E]₀^∞ = 0` (`E(r) = a⁻²(2 - r²/(2a))e^{-r²/(4a)}`, `(r²E)' = (rE' + 2E) r`). -/
def PlaneZero : Prop :=
  ∀ a : ℝ, 1 ≤ a → (∫ x : ℝ × ℝ, hMode a x) = 0 ∧ (∫ x : ℝ × ℝ, rMode a x) = 0

/-- **Pointwise continuity of the periodized sources in the age** (source 4565, `a(t) = 1 + νt`;
`srcA ν s = 1 + ν max s 0`): for `ν > 0` and each `x`, `s ↦ HProf ν (cOf ν) s x` and
`s ↦ RProf ν (cOf ν) s x` are continuous.  Route: `a ↦ hMode a y`, `rMode a y` continuous on `a > 0`
(`gaussE`, `gaussRdE` closed forms; `gaussRdE a r = -a⁻²(r²/(2a))(4 - r²/(2a))e^{-r²/(4a)}`), `s ↦ srcA ν s`
continuous with values `≥ 1`, and `continuous_tsum` (Weierstrass M-test with the Gaussian bound
`GaussPointBound` on `A = srcA ν S`, locally in `s`, summable over the lattice). -/
def GaussProfPtCont : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ x : ℝ × ℝ,
    Continuous (fun s => HProf ν (cOf ν) s x) ∧ Continuous (fun s => RProf ν (cOf ν) s x)

/-- **Continuity of the sources in the age** (source 4565: `a(t) = 1 + νt`; `srcA ν s = 1 + ν max s 0`):
any family `F s ∈ L²(cellMeasure)` pinned to `HProf ν (cOf ν) s` (resp. `RProf`) is continuous in `s`.
Route (given `GaussProfPtCont`, `PeriodizePointBound`, `GaussPointBound`): continuity into `L²` by dominated convergence (`Pair.continuousToLpOfDominated` in
`Concrete/FlatSettingInst/Pair/Proofs/ContinuousToLpOfDominated.lean`, with `F s := (hF s).toLp`)
applied to `s ↦ F (min s S)` for each `S` (equal to `F` on `s ≤ S`); domination by
`g x = C e^{-|x|²/(16 A_S)}` with `A_S = srcA ν S` from `GaussPointBound` and the pointwise bound of
`PeriodizeL2Bound`'s proof (hence `MemLp g 2` on the cell: Gaussian); pointwise continuity of
`s ↦ HProf ν c s x`: `a ↦ hMode a y`, `rMode a y` is continuous for `a > 0` (`gaussE`, `gaussRdE`
closed forms) and the lattice sum converges locally uniformly in `a` (Weierstrass M-test,
`continuous_tsum`). -/
def GaussSrcContinuous : Prop :=
  ∀ (ν m : ℝ), 0 < ν →
    (∀ F : ℝ → XAmb (cOf ν) m,
      (∀ s, (F s : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure (cOf ν) m] HProf ν (cOf ν) s) → Continuous F) ∧
    (∀ F : ℝ → XAmb (cOf ν) m,
      (∀ s, (F s : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure (cOf ν) m] RProf ν (cOf ν) s) → Continuous F)

/-! ## Assembly -/

theorem angTwo_neg (x : ℝ × ℝ) : IIIa.angTwo (-x) = IIIa.angTwo x := by
  unfold IIIa.angTwo
  simp only [Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg]
  have : (-(x.1 : ℂ) + -(x.2 : ℂ) * Complex.I) ^ 2 = ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2 := by
    ring
  rw [this]
  congr 2
  ring

theorem planeR_neg (x : ℝ × ℝ) : planeR (-x) = planeR x := by
  simp [planeR]

theorem hMode_even (a : ℝ) (x : ℝ × ℝ) : hMode a (-x) = hMode a x := by
  simp [hMode, planeR_neg, angTwo_neg]

theorem rMode_even (a : ℝ) (x : ℝ × ℝ) : rMode a (-x) = rMode a x := by
  simp [rMode, planeR_neg]

theorem periodizeC_even (c : ℝ) (g : ℝ × ℝ → ℂ) (he : ∀ x, g (-x) = g x) (x : ℝ × ℝ) :
    IIIa.periodizeC c g (-x) = IIIa.periodizeC c g x := by
  unfold IIIa.periodizeC
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => g (x.1 - n * c, x.2))]
  refine tsum_congr fun n => ?_
  rw [← he]
  congr 1
  ext <;> simp <;> ring

/-- An element of `X_{m,c}` pinned to a periodization with the stated properties. -/
theorem exists_elem {c m : ℝ} [Fact (1 < m)] (g : ℝ × ℝ → ℂ)
    (hg : MemLp (IIIa.periodizeC c g) 2 (B0579.cellMeasure c m))
    (hcirc : ∫ x in B0579.cell c, IIIa.periodizeC c g x = 0)
    (heven : ∀ x, IIIa.periodizeC c g (-x) = IIIa.periodizeC c g x) :
    ∃ x : Xmc c m, xFn x =ᵐ[volume.restrict (B0579.cell c)] IIIa.periodizeC c g := by
  obtain ⟨f, hco⟩ : ∃ f : XAmb c m, (f : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m]
      IIIa.periodizeC c g := ⟨hg.toLp _, hg.coeFn_toLp⟩
  have hcell := ae_cell_of_ae_cellMeasure hco
  have hmem : f ∈ xmcSub c m := by
    rw [mem_xmcSub]
    refine ⟨?_, ?_⟩
    · rw [integral_congr_ae hcell]; exact hcirc
    · refine Lp.ext ?_
      have h1 := coeFn_reflX (c := c) (m := m) f
      have h2' : ∀ᵐ x ∂(B0579.cellMeasure c m), (f : ℝ × ℝ → ℂ) (-x) =
          IIIa.periodizeC c g (-x) :=
        (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae (p := fun y => (f : ℝ × ℝ → ℂ) y =
          IIIa.periodizeC c g y) hco
      have h2 : (fun x : ℝ × ℝ => f (-x)) =ᵐ[B0579.cellMeasure c m]
          fun x => IIIa.periodizeC c g (-x) := h2'
      exact h1.trans (h2.trans ((Filter.EventuallyEq.of_eq (funext heven)).trans hco.symm))
  exact ⟨⟨f, hmem⟩, hcell⟩

theorem gaussSourcesExist_of (h1 : GaussPointBound) (h2 : GaussMeasurable)
    (h3 : PeriodizeL2Bound) (h4 : PeriodizeIntegral) (h5 : PlaneIntegrable) (h6 : PlaneZero)
    (h7 : GaussSrcContinuous) : GaussSourcesExist := by
  intro ν m _ hν
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hmode : ∀ s : ℝ, ∃ xh xr : Xmc (cOf ν) m,
      xFn xh =ᵐ[volume.restrict (B0579.cell (cOf ν))] HProf ν (cOf ν) s ∧
      xFn xr =ᵐ[volume.restrict (B0579.cell (cOf ν))] RProf ν (cOf ν) s := by
    intro s
    have hA : 1 ≤ srcA ν s := by
      unfold srcA ageA
      have : 0 ≤ ν * max s 0 := mul_nonneg hν.le (le_max_right _ _)
      linarith
    obtain ⟨C, hC⟩ := h1 (srcA ν s) hA
    obtain ⟨C3, hC3⟩ := h3 m (srcA ν s) (cOf ν) (by linarith) hc
    have hb := fun x => hC (srcA ν s) ⟨hA, le_rfl⟩ x
    obtain ⟨hmH, hmR⟩ := h2 (srcA ν s)
    obtain ⟨hiH, hiR⟩ := h5 _ hA
    obtain ⟨hzH, hzR⟩ := h6 _ hA
    have hH := hC3 (cOf ν) le_rfl (hMode (srcA ν s)) C hmH (fun x => (hb x).1)
    have hR := hC3 (cOf ν) le_rfl (rMode (srcA ν s)) C hmR (fun x => (hb x).2)
    have mH : MemLp (IIIa.periodizeC (cOf ν) (hMode (srcA ν s))) 2
        (B0579.cellMeasure (cOf ν) m) :=
      ⟨hH.1, lt_of_le_of_lt hH.2 ENNReal.ofReal_lt_top⟩
    have mR : MemLp (IIIa.periodizeC (cOf ν) (rMode (srcA ν s))) 2
        (B0579.cellMeasure (cOf ν) m) :=
      ⟨hR.1, lt_of_le_of_lt hR.2 ENNReal.ofReal_lt_top⟩
    obtain ⟨xh, hxh⟩ := exists_elem (hMode (srcA ν s)) mH
      (by rw [h4 _ _ hc hiH]; exact hzH)
      (periodizeC_even _ _ (hMode_even _))
    obtain ⟨xr, hxr⟩ := exists_elem (hMode (srcA ν s) |> fun _ => rMode (srcA ν s)) mR
      (by rw [h4 _ _ hc hiR]; exact hzR)
      (periodizeC_even _ _ (rMode_even _))
    exact ⟨xh, xr, hxh, hxr⟩
  choose xh xr hxh hxr using hmode
  obtain ⟨hcH, hcR⟩ := h7 ν m hν
  refine ⟨⟨fun s => xh s, fun s => xr s, hxh, hxr, ?_, ?_⟩⟩
  · have := hcH (fun s => ((xh s : Xmc (cOf ν) m) : XAmb (cOf ν) m))
      (fun s => ae_cellMeasure_of_ae_cell (hxh s))
    exact continuous_induced_rng.2 this
  · have := hcR (fun s => ((xr s : Xmc (cOf ν) m) : XAmb (cOf ν) m))
      (fun s => ae_cellMeasure_of_ae_cell (hxr s))
    exact continuous_induced_rng.2 this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
