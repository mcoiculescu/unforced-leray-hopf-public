import UnforcedLeray.Short.PartIIb.Sub.G4_3_org

/-!
# Part II-b, task `PartII-b:G4/3/7` (`ColumnMem`): decomposition

Source of record: `the November 2 reference manuscript` (SP), lines 2347-2348,
2370-2374, 2385 ("The integrability exponent is `-9/8 + p = 13/8 > -1`").

`ColumnMem` (each column `colEps p i` lies in `H_p`) follows from
* `ColQPeriodic` (the column is `c`-periodic in `q`; inlet and train profiles are periodic),
* `ColAEMeas` (the column is a.e. strongly measurable: continuous on `s > 0`),
* `ColEnvelope` (the column vanishes for `s ≥ H/2` and for `0 < s ≤ H/2` is bounded by
  `A ν^{-k} s (1+|η|)^N e^{-κ|η|/c}`, from the jets of the inlet profile and `RawJetBound`),
* `ColWeightNorm` (the weighted `H_p` norm of such an envelope is finite and polynomially bounded:
  `∫_0^{H/2} s^{-9/8 + 11/4} ds < ∞`, SP 2385).

Proved here: `columnMem_of_parts`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- The standing setting of the column lemmas: regime, small `ν`, slow age `Σ`, eigenmode `q`. -/
def ColReg (Sig : ℝ) (q : Blueprint.Planar.Profile) (dm dp ν₀ : ℝ) (p : Params) (d : ℝ) : Prop :=
  BgRegime p d dm dp ∧ p.ν ≤ ν₀ ∧ p.ageCut = Sig ∧ p.mode = q

/-- **Weighted `H_p` norm of an envelope** (SP 2385): if `f` vanishes for `s > H/2` and satisfies
`‖f x‖ ≤ M s (1+|η|)^N e^{-κ|η|/c}` for `0 < s ≤ H/2` then (`p = 11/4`, weight `s^{-9/8}`)
`‖f‖_{H_p} ≤ K M (1+H) c^{N+1}`, `K` depending only on `N, κ`.
(Proof: `eLpNorm_mono_ae` against the measurable majorant, `Axi.lintegral_ageμ`; the age integral is
`∫_0^{H/2} s^{13/8} ds = (8/21)(H/2)^{21/8}` and its `1/p` power is `≤ 1+H`; the cell has width `c`
which cancels the `c⁻¹`; the `η`-integral `∫(1+|η|)^{Np} e^{-pκ|η|/c} dη ≤ K' c^{Np+1}`, whose
`1/p` power is `≤ K c^{N+1}` for `c ≥ 1`.) -/
def ColWeightNorm : Prop :=
  ∀ (N : ℕ) (κ : ℝ), 0 < κ → ∃ K : ℝ, 0 < K ∧
    ∀ (c H M : ℝ) (f : CProf), 1 ≤ c → 0 < H → 0 ≤ M →
      (∀ x : Coord, H / 2 < x.1 → f x = 0) →
      (∀ x : Coord, 0 < x.1 → x.1 ≤ H / 2 →
        ‖f x‖ ≤ M * x.1 * (1 + |x.2.2|) ^ N * Real.exp (-(κ * |x.2.2| / c))) →
      hNorm c bgp f ≤ ENNReal.ofReal (K * M * (1 + H) * c ^ (N + 1))

/-- **The column is `c`-periodic in `q`** (SP 2347-2348: the inlet profile is built from the
periodized stream `periodicStream q c`; the train is `c`-periodic; `colEpsR` is built from
`inletProfile`, `rawProf` and their chart derivatives, and is `0` for `s ≤ 0`). -/
def ColQPeriodic : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      QPeriodic p.c (colEps p i)

/-- **The column is a.e. strongly measurable** for the `H_p` measure (it is continuous on `s > 0`:
inlet profile `C^∞`, train `C^∞` on `s > 0`; and `0` for `s ≤ 0`; the measure lives on `s > 0`). -/
def ColAEMeas : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      AEStronglyMeasurable (colEps p i) (hMeas p.c bgp)

/-- **Pointwise envelope of the column** (SP 2370-2374, 2385). -/
def ColEnvelope : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (A κ : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < A ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      (∀ x : Coord, p.H / 2 < x.1 → colEpsR p i x = 0) ∧
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H / 2 →
        ‖colEpsR p i x‖ ≤ A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
          Real.exp (-(κ * |x.2.2| / p.c))

/-- **`ColumnMem` from its four parts.** -/
theorem columnMem_of_parts (hW : ColWeightNorm) (hP : ColQPeriodic) (hM : ColAEMeas)
    (hE : ColEnvelope) : ColumnMem := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨A, κ, k, N, ν₀, hA, hκ, hν₀, hν₀1, HE⟩ := hE Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, HP⟩ := hP Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HM⟩ := hM Sig lam q hSig hq dm dp hdm
  obtain ⟨K, hK, HW⟩ := hW N κ hκ
  refine ⟨min ν₀ (min ν₁ ν₂), lt_min hν₀ (lt_min hν₁ hν₂), ?_⟩
  intro p d hreg hν hS hm i
  have h0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ ν₁ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := h0.trans hν₀1
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hH : 0 < p.H := div_pos p.ageCut_pos hνpos
  obtain ⟨hvan, hbd⟩ := HE p d ⟨hreg, h0, hS, hm⟩ i
  refine ⟨HP p d ⟨hreg, h1, hS, hm⟩ i, HM p d ⟨hreg, h2, hS, hm⟩ i, ?_⟩
  have hMnn : 0 ≤ A * (p.ν ^ k)⁻¹ := by positivity
  have hle := HW p.c p.H (A * (p.ν ^ k)⁻¹) (colEps p i) hc1 hH hMnn
    (fun x hx => by
      have := hvan x hx
      ext j
      simp [colEps, cplx, this])
    (fun x hx0 hx1 => by
      have e : ‖colEps p i x‖ = ‖colEpsR p i x‖ := liftM_norm _
      rw [e]
      exact hbd x hx0 hx1)
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-! ## The pointwise envelope: parts -/

/-- The first-order jet norm `‖G‖ + ‖∂_qG‖ + ‖∂_ηG‖ + ‖KG‖` of a chart profile at a point (the
quantities bounded by `RawJetBound`). -/
def chartJet (G : Coord → Axi.Merid) (x : Coord) : ℝ :=
  ‖G x‖ + ‖Axi.dQ G x‖ + ‖Axi.dEta G x‖ + ‖kAge G x‖

/-- The meridional field `H e_z` (`e_z = m1`) of the raised stream. -/
def raisedMerid (p : Params) : Coord → Axi.Merid := fun x => raisedProf p x • Axi.m1

/-- `b_raw = v + εHe_z` (SP 1206-1216, 2419). -/
theorem rawProf_eq (p : Params) :
    rawProf p = fun x => trainProf p x + p.ε • raisedMerid p x := by
  funext x
  simp [rawProf, trainProf, raisedMerid, raisedProf, UnforcedLeray.Cons.C03.rawProfile,
    Axi.m1, smul_smul]

/-- **Jets of the raw profile from `RawJetBound`** (SP 2419-2423): on `0 < s ≤ H` the jet norms of
`v`, `He_z` and `b_raw = v + εHe_z` are bounded by `Cν^{-k}(1+|η|)^N` (`ε ≤ 1`; the jet norm of
`He_z` is at most that of the scalar `H`; `rawProf_eq`; differentiability on `s > 0` from
`BgRegime.train_stream_smooth`). -/
def RawProfJet : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k N : ℕ) (ν₀ : ℝ),
    0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
        chartJet (trainProf p) x ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N ∧
        chartJet (raisedMerid p) x ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N ∧
        chartJet (rawProf p) x ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N

/-- **Jets of the inlet profile with transverse decay** (SP 2347-2358, 2360-2369): the inlet
profile `ringStreamProfile R (cutStream i)` (`cutStream = χ(s) ψ_i`) has all derivatives of order
`≤ 2` bounded by `Cν^{-k}e^{-κ|η|/c}` (from `cutStreamJets`, which keeps the decay; the ring
formula `(-φ_η, φ_q + ε(φ - 2sφ_s - ηφ_η))` with `s ≤ H/2` on the support of `φ_s` and
`|η|e^{-κ|η|/c} ≤ (2c/κ)e^{-κ|η|/(2c)}`; `κ` may be halved). Compare `InletProfileJets`, which
has no decay. -/
def InletJetDecay : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C κ : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      ContDiff ℝ ∞ (p.inletProfile i) ∧
      ∀ l ≤ 2, ∀ x : Coord, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
        C * (p.ν ^ k)⁻¹ * Real.exp (-(κ * |x.2.2| / p.c))

/-- **First-order chart calculus** (pure calculus): for a `C^∞` meridional chart profile `F`, the
chart derivatives and the Euler field `K = 2s∂_s + η∂_η` are bounded by the jets of `F`. -/
def JetLe : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F → ∀ x : Coord,
    chartJet F x + ‖Axi.dS F x‖ ≤
      K * (1 + |x.1| + |x.2.2|) * ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l F x‖

/-- **Second-order chart calculus** (pure calculus; `vecDiffEps` is
`∂_q² F + ∂_η² F - 2ε(K∂_qF + ∂_qF) + ε²(K(KF + F) + KF + F - diag(1,0)F)`): for `C^∞` `F` and
`0 ≤ ε ≤ 1`, `‖L_εF‖` is bounded by the jets of `F` of order `≤ 2`. -/
def VecDiffJet : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 → ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F →
    ∀ x : Coord, ‖vecDiffEps ε F x‖ ≤
      K * (1 + |x.1| + |x.2.2|) ^ 2 * ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l F x‖

/-- **The interaction is bilinear in the jets** (pure algebra from the definitions of `bEps`,
`qEps`, `chartJet`): for `0 ≤ ε ≤ 1`, `‖B_εF‖ ≤ 6 J(b_raw) J(F)`. -/
def BEpsJet : Prop :=
  ∀ (p : Params), 0 ≤ p.ε → p.ε ≤ 1 → ∀ (F : Coord → Axi.Merid) (x : Coord),
    ‖bEps p F x‖ ≤ 6 * chartJet (rawProf p) x * chartJet F x

/-- **The column vanishes beyond the cutoff** (SP 2360-2366: `χ(s) = 0` for `s ≥ H/2`, so the
inlet profile vanishes on the open set `s > H/2`, with all its derivatives; `colDiffR`, `colIntR`
are built from it). -/
def ColVanish : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      ∀ x : Coord, p.H / 2 < x.1 → colEpsR p i x = 0

end UnforcedLeray.Short.IIb

end
