import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.FlatUniform

/-!
# `PartIII-b:IIIb-D3/2/G2/org`: group G2 (the Gaussian comparison) from four leaves

Source of record: `the November 2 reference manuscript`: 4650-4654
(`ℓ_{+,νt,c} H_{t,c} = ℓ₊(H₀) + O(νt + c⁻²)`, conjugate-`H` and `R` pairings `O(c⁻²)`,
`0 ≤ t ≤ 1.1/ν`), 4562-4577 (Gaussian sources), frozen pair 2894-2912, 4352-4356.

Mathematics.  The frozen dual `ℓ_{+,s}f = ∫_{cell d} Λ₊ · J_a⁻¹f` with `a = 1+νs`, `d = c/√a`.
For the sources the scaling is exact: `J_a⁻¹ H_{s,c} = P_d(hMode 1)` (Gaussian self-similarity
`gaussRdE a r = a⁻² gaussRdE 1 (r/√a)`, `angTwo` is scale invariant), likewise for `H̄`, `R`.  So no
`νt` error occurs.  The Gram matrix and the periodized dual row converge to the planar ones with
error `O(d⁻²)` (Gaussian `e_j`, `|λ_i| ≲ (1+|y|)⁻²`), and `d ≥ c/2` on the window, so
`ℓ₊H = ∫ λ₀ hMode 1 + O(c⁻²)`; `∫ λ₀ hMode 1 = Pl.strainCoupling` is `SeedLink`
(the normalization link is the right one: the Gram-normalized periodized dual row tends to `lamP`),
and the three other integrals vanish by sector orthogonality (`λ₀` reads sector `2`, `λ₁` sector `-2`).

Leaves (Props below): `FrozenReduce`, `ModeBounds`, `PairNear`, `SectorOrth`.
Assembly: `flatGroupGauss_of`; the task `PartIII-b:IIIb-D3/2/G2` states
`flatGroupGauss D := flatGroupGauss_of frozenReduce modeBounds pairNear sectorOrth D`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2

open FlatSettingInst

/-- Leaf A (exact scaling, source 4352-4356, 4562-4570, 2894-2912): for `0 ≤ t ≤ 1.1/ν` (band age
`= t`), the frozen dual of a function a.e. equal on the cell to the source `H`, `H̄`, `R` equals the
pairing of `Λ₊` with the periodization (at cell length `d = c/√(1+νt)`) of the unit-clock mode:
`J_a⁻¹ H_{t,c} = P_d(hMode 1)`, `J_a⁻¹ conj H_{t,c} = P_d(conj ∘ hMode 1)`, `J_a⁻¹ R_{t,c} =
P_d(rMode 1)`. -/
def FrozenReduce : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν : ℝ), 0 < ν → ∀ t ∈ Icc (0 : ℝ) (1.1 / ν), ∀ (j : Bool)
    (f : ℝ × ℝ → ℂ),
    (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] HProf ν (cOf ν) t →
      frozenEll κ ν (cOf ν) j t f =
        ∫ y in B0579.cell (cOf ν / Real.sqrt (1 + ν * t)),
          IIIa.perLam κ (cOf ν / Real.sqrt (1 + ν * t)) (pmIdx j) y *
            IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) (hMode 1) y) ∧
    (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] (fun p => conj (HProf ν (cOf ν) t p)) →
      frozenEll κ ν (cOf ν) j t f =
        ∫ y in B0579.cell (cOf ν / Real.sqrt (1 + ν * t)),
          IIIa.perLam κ (cOf ν / Real.sqrt (1 + ν * t)) (pmIdx j) y *
            IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) (fun p => conj (hMode 1 p)) y) ∧
    (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] RProf ν (cOf ν) t →
      frozenEll κ ν (cOf ν) j t f =
        ∫ y in B0579.cell (cOf ν / Real.sqrt (1 + ν * t)),
          IIIa.perLam κ (cOf ν / Real.sqrt (1 + ν * t)) (pmIdx j) y *
            IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) (rMode 1) y)

/-- Leaf B: the unit modes `hMode 1`, `rMode 1` are continuous with Gaussian decay
(`gaussE 1 r = (2 - r²/2)e^{-r²/4}`, source 4565-4570). -/
def ModeBounds : Prop :=
  Continuous (hMode 1) ∧ Continuous (rMode 1) ∧
    ∃ K : ℝ, ∀ y : ℝ × ℝ, ‖hMode 1 y‖ ≤ K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ∧
      ‖rMode 1 y‖ ≤ K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)

/-- Leaf C (periodized dual row, source 2894-2912): for planar frame kernels and a continuous
Gaussian-decaying `g`, `Λ_i = G⁻¹Λ⁰` paired with `P_d g` on the cell is `∫ λ_i g + O(d⁻²)`
(the Gram matrix is `1 + O(d⁻²)`: unfolding `∫_cell Λ⁰_i P_d g = ∑_m ∫ λ_i g(·-md)`). -/
def PairNear : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (g : ℝ × ℝ → ℂ), Continuous g →
    (∃ K : ℝ, ∀ y : ℝ × ℝ, ‖g y‖ ≤ K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
    ∃ C d0 : ℝ, 0 < d0 ∧ ∀ d : ℝ, d0 ≤ d → ∀ i : Fin 2,
      ‖(∫ y in B0579.cell d, IIIa.perLam κ d i y * IIIa.periodizeC d g y) -
          ∫ y, κ.lamP i y * g y‖ ≤ C * d⁻¹ ^ 2

/-- Leaf D (sector orthogonality of the seed kernels, source 593-610, 2891-2897): `λ₁` annihilates
the sector-`2` mode `hMode 1`, `λ₀` the sector `-2` mode `conj hMode 1`, both the sector-`0` mode
`rMode 1`. -/
def SectorOrth : Prop :=
  ∀ κ : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ →
    (∫ y, κ.lamP 1 y * hMode 1 y) = 0 ∧ (∫ y, κ.lamP 0 y * conj (hMode 1 y)) = 0 ∧
      (∀ i : Fin 2, ∫ y, κ.lamP i y * rMode 1 y = 0)

/-- Pairing helper: from `PairNear` at `g` and `∫ λ₀ g = target`, the `i = 0` pairing is within
`C c⁻²` of `target` on the window once `d₀ ≤ c/2`. -/
theorem pair_helper (κ : IIIa.PlanarFrameKernels) (g : ℝ × ℝ → ℂ) (target : ℂ)
    (hint : (∫ y, κ.lamP 0 y * g y) = target)
    (hP : ∃ C d0 : ℝ, 0 < d0 ∧ ∀ d : ℝ, d0 ≤ d → ∀ i : Fin 2,
      ‖(∫ y in B0579.cell d, IIIa.perLam κ d i y * IIIa.periodizeC d g y) -
          ∫ y, κ.lamP i y * g y‖ ≤ C * d⁻¹ ^ 2) :
    ∃ C d0 : ℝ, 0 < d0 ∧ ∀ ν : ℝ, 0 < ν → ∀ t ∈ Icc (0 : ℝ) (1.1 / ν), d0 ≤ cOf ν / 2 →
      ‖(∫ y in B0579.cell (cOf ν / Real.sqrt (1 + ν * t)),
          IIIa.perLam κ (cOf ν / Real.sqrt (1 + ν * t)) 0 y *
            IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) g y) - target‖ ≤
        C * (cOf ν)⁻¹ ^ 2 := by
  obtain ⟨C, d0, hd0, H⟩ := hP
  refine ⟨4 * |C|, d0, hd0, fun ν hν t ht hd => ?_⟩
  have hc : 0 < cOf ν := cOf_pos hν
  have hνt : ν * t ≤ 1.1 := by
    have := ht.2
    rw [le_div_iff₀ hν] at this
    linarith
  have hνt0 : 0 ≤ ν * t := mul_nonneg hν.le ht.1
  have hs : Real.sqrt (1 + ν * t) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num at hνt ⊢; linarith)
  have hs1 : 1 ≤ Real.sqrt (1 + ν * t) := Real.one_le_sqrt.mpr (by linarith)
  have hd2 : cOf ν / 2 ≤ cOf ν / Real.sqrt (1 + ν * t) :=
    div_le_div_of_nonneg_left hc.le (by linarith) hs
  have hdd : d0 ≤ cOf ν / Real.sqrt (1 + ν * t) := le_trans hd hd2
  have hpos : 0 < cOf ν / 2 := by positivity
  have h1 := H _ hdd 0
  rw [hint] at h1
  refine h1.trans ?_
  have hinv : (cOf ν / Real.sqrt (1 + ν * t))⁻¹ ≤ 2 * (cOf ν)⁻¹ := by
    rw [inv_div, div_le_iff₀ hc]
    calc Real.sqrt (1 + ν * t) ≤ 2 := hs
      _ = 2 * (cOf ν)⁻¹ * cOf ν := by field_simp
  have hinv0 : 0 ≤ (cOf ν / Real.sqrt (1 + ν * t))⁻¹ := by positivity
  have hsq : (cOf ν / Real.sqrt (1 + ν * t))⁻¹ ^ 2 ≤ (2 * (cOf ν)⁻¹) ^ 2 :=
    pow_le_pow_left₀ hinv0 hinv 2
  calc C * (cOf ν / Real.sqrt (1 + ν * t))⁻¹ ^ 2 ≤ |C| * (cOf ν / Real.sqrt (1 + ν * t))⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * (cOf ν)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
    _ = 4 * |C| * (cOf ν)⁻¹ ^ 2 := by ring

/-- The three window bounds of `FlatGaussComparison`, uniform in the level (`c = cOf ν`). -/
theorem core (hred : FrozenReduce) (hmod : ModeBounds) (hpair : PairNear) (hsec : SectorOrth)
    (κ : IIIa.PlanarFrameKernels) (hκ : IIIa.IsSeedKernels κ) (ell : ℂ)
    (hell : (∫ y, κ.lamP 0 y * hMode 1 y) = ell) :
    ∃ C d0 : ℝ, 0 < d0 ∧ ∀ ν : ℝ, 0 < ν → ∀ t ∈ Icc (0 : ℝ) (1.1 / ν), d0 ≤ cOf ν / 2 →
      ∀ f : ℝ × ℝ → ℂ,
        (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] HProf ν (cOf ν) t →
          ‖frozenEll κ ν (cOf ν) true t f - ell‖ ≤ C * (cOf ν)⁻¹ ^ 2) ∧
        (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] (fun p => conj (HProf ν (cOf ν) t p)) →
          ‖frozenEll κ ν (cOf ν) true t f‖ ≤ C * (cOf ν)⁻¹ ^ 2) ∧
        (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] RProf ν (cOf ν) t →
          ‖frozenEll κ ν (cOf ν) true t f‖ ≤ C * (cOf ν)⁻¹ ^ 2) := by
  obtain ⟨hc1, hc2, K, hK⟩ := hmod
  obtain ⟨_, hs2, hs3⟩ := hsec κ hκ
  have hdecH : ∃ K : ℝ, ∀ y : ℝ × ℝ, ‖hMode 1 y‖ ≤ K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨K, fun y => (hK y).1⟩
  have hdecC : ∃ K : ℝ, ∀ y : ℝ × ℝ, ‖conj (hMode 1 y)‖ ≤ K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨K, fun y => by simpa using (hK y).1⟩
  have hdecR : ∃ K : ℝ, ∀ y : ℝ × ℝ, ‖rMode 1 y‖ ≤ K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨K, fun y => (hK y).2⟩
  obtain ⟨C1, e1, he1, H1⟩ := pair_helper κ (hMode 1) ell hell
    (hpair κ (hMode 1) hc1 hdecH)
  obtain ⟨C2, e2, he2, H2⟩ := pair_helper κ (fun p => conj (hMode 1 p)) 0 hs2
    (hpair κ _ (Complex.continuous_conj.comp hc1) hdecC)
  obtain ⟨C3, e3, he3, H3⟩ := pair_helper κ (rMode 1) 0 (hs3 0)
    (hpair κ (rMode 1) hc2 hdecR)
  refine ⟨max C1 (max C2 C3), max e1 (max e2 e3), lt_max_of_lt_left he1, fun ν hν t ht hd f => ?_⟩
  have hd1 : e1 ≤ cOf ν / 2 := le_trans (le_max_left _ _) hd
  have hd2 : e2 ≤ cOf ν / 2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hd3 : e3 ≤ cOf ν / 2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hsq : 0 ≤ (cOf ν)⁻¹ ^ 2 := by positivity
  obtain ⟨r1, r2, r3⟩ := hred κ ν hν t ht true f
  refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
  · rw [r1 hf]
    have := H1 ν hν t ht hd1
    simp only [pmIdx, ite_true] at this ⊢
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsq)
  · rw [r2 hf]
    have := H2 ν hν t ht hd2
    simp only [pmIdx, ite_true, sub_zero] at this ⊢
    exact this.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_right _ _)) hsq)
  · rw [r3 hf]
    have := H3 ν hν t ht hd3
    simp only [pmIdx, ite_true, sub_zero] at this ⊢
    exact this.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right _ _) (le_max_right _ _)) hsq)

/-- The three bounds for the actual level setting (`levelFlat`), from `core`. -/
theorem level_bounds {ν m : ℝ} [Fact (1 < m)] {κ : IIIa.PlanarFrameKernels}
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (hν : 0 < ν)
    (FI : FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε : ℝ) (ell : ℂ) (C : ℝ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1.1 / ν))
    (key : ∀ f : ℝ × ℝ → ℂ,
        (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] HProf ν (cOf ν) t →
          ‖frozenEll κ ν (cOf ν) true t f - ell‖ ≤ C * (cOf ν)⁻¹ ^ 2) ∧
        (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] (fun p => conj (HProf ν (cOf ν) t p)) →
          ‖frozenEll κ ν (cOf ν) true t f‖ ≤ C * (cOf ν)⁻¹ ^ 2) ∧
        (f =ᵐ[volume.restrict (B0579.cell (cOf ν))] RProf ν (cOf ν) t →
          ‖frozenEll κ ν (cOf ν) true t f‖ ≤ C * (cOf ν)⁻¹ ^ 2)) :
    ‖((levelFlat hν FI χo ε).pk.ell true t) ((levelFlat hν FI χo ε).Hper t) - ell‖ ≤
        C * (cOf ν)⁻¹ ^ 2 ∧
      ‖((levelFlat hν FI χo ε).pk.ell true t)
        ((levelFlat hν FI χo ε).conjX ((levelFlat hν FI χo ε).Hper t))‖ ≤ C * (cOf ν)⁻¹ ^ 2 ∧
      ‖((levelFlat hν FI χo ε).pk.ell true t) ((levelFlat hν FI χo ε).Rper t)‖ ≤
        C * (cOf ν)⁻¹ ^ 2 := by
  have hHc : xFn (conjX (FI.src.H t)) =ᵐ[volume.restrict (B0579.cell (cOf ν))]
      fun p => conj (HProf ν (cOf ν) t p) := by
    filter_upwards [xFn_conjX (FI.src.H t), FI.src.H_pin t] with p h1 h2
    rw [h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · show ‖FI.pair.ell true t (FI.src.H t) - ell‖ ≤ _
    rw [FI.pair.ell_pin]
    exact (key _).1 (FI.src.H_pin t)
  · show ‖FI.pair.ell true t (conjX (FI.src.H t))‖ ≤ _
    rw [FI.pair.ell_pin]
    exact (key _).2.1 hHc
  · show ‖FI.pair.ell true t (FI.src.R t)‖ ≤ _
    rw [FI.pair.ell_pin]
    exact (key _).2.2 (FI.src.R_pin t)

/-- **Group G2 from the four leaves** (source 4650-4654). -/
theorem flatGroupGauss_of (hred : FrozenReduce) (hmod : ModeBounds) (hpair : PairNear)
    (hsec : SectorOrth) (D : SeqData) : GroupGauss D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨hκs, hlink⟩ := hκ
  obtain ⟨C, d0, hd0, H⟩ := core hred hmod hpair hsec κ hκs D.Pl.strainCoupling hlink
  have hT := retNu_tendsto (Pl := D.Pl) D.σ₀ hst.omega_ne
  have hev : ∀ᶠ n : ℕ in atTop, d0 ≤ cOf (retNu D.Pl D.σ₀ n) / 2 := by
    have hlim : Tendsto (fun n : ℕ => cOf (retNu D.Pl D.σ₀ n)) atTop atTop := by
      have h0 : Tendsto (fun n : ℕ => retNu D.Pl D.σ₀ n ^ 2) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
        · simpa using hT.pow 2
        · exact pow_pos (retNu_pos D.Pl D.σ₀ n) 2
      exact tendsto_inv_nhdsGT_zero.comp h0
    exact (tendsto_atTop.1 hlim (2 * d0)).mono fun n hn => by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hS.and hev)
  refine ⟨|C|, N, fun n hn t ht => ?_⟩
  obtain ⟨⟨FI, hFI⟩, hdn⟩ := hN n hn
  have hν := retNu_pos D.Pl D.σ₀ n
  have hc : 0 < cOf (retNu D.Pl D.σ₀ n) := cOf_pos hν
  have key := H _ hν t ht hdn
  have hnn : 0 ≤ (cOf (retNu D.Pl D.σ₀ n))⁻¹ ^ 2 := by positivity
  have hCa : C * (cOf (retNu D.Pl D.σ₀ n))⁻¹ ^ 2 ≤ |C| * (cOf (retNu D.Pl D.σ₀ n))⁻¹ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hnn
  have hnt : 0 ≤ retNu D.Pl D.σ₀ n * t := mul_nonneg hν.le ht.1
  have hbig : |C| * (cOf (retNu D.Pl D.σ₀ n))⁻¹ ^ 2 ≤
      |C| * (retNu D.Pl D.σ₀ n * t + (cOf (retNu D.Pl D.σ₀ n))⁻¹ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  rw [hFI]
  obtain ⟨b1, b2, b3⟩ := level_bounds hν FI D.K.χo (retEps D.Pl D.σ₀ n) D.Pl.strainCoupling C t ht key
  exact ⟨b1.trans (hCa.trans hbig), b2.trans (hCa.trans le_rfl), b3.trans (hCa.trans le_rfl)⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2
