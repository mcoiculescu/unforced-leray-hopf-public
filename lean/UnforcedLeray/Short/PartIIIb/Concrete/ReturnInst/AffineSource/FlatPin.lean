import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting

/-!
# The pin of the per-level flat setting (source 4557-4612)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (d) of `ORG:return-concrete/instance-3/affine-source`.  `SeqData` (`Concrete/ReturnInst.lean`)
carries a flat setting `D.flat n : ConcreteYF.FlatSetting` at every level, a structure with free
fields.  The source's flat setting at level `n` (source 4557-4612: `c = ν⁻²`, the actual cylinder
train in the evolution, the Gaussian sources `H_{s,c}, R_{s,c}`, the readout
`M = v ⊗ K_cξ + K_cξ ⊗ v`, `χ_o(s) = χ̂_o(νs)`, amplitude `ε³`) is
`FlatSettingInst.actualFlatSetting FI χ̂_o ε_n` for the pinned data `FI : FlatInstData κ ν_n c_n m
(D.train n)` of the actual train of the level (`Concrete/FlatSettingInst/Setting.lean`).

* `levelFlat hν FI χo ε` : that setting at cell size `c = ν⁻²` (the instance `Fact (0 < c)` from
  `hν : 0 < ν`);
* `SeqData.IsActualFlat D κ m n` : **the pin** `D.flat n = levelFlat … FI D.K.χo ε_n` for some
  `FI`.  The kernels `κ` enter only the frozen pair `q_±, ℓ_±` of the package (not `𝔗`, which uses
  the train evolution, the sources and the readout); at the instance they are the planar seed
  kernels (`IIIa.IsSeedKernels κ`, existence `IIIa.PlanarFrameKernelsExist`), and `m > 1` is the
  weight of `X_{m,c}` (source 4349-4350);
* `SeqData.IsActualFlat.frakT_eq` : under the pin, `𝔗` of the level is that of `levelFlat`.

`Concrete/FlatSettingInst/Setting.lean` imports together with `Concrete/ReturnInst.lean` (this
file compiles).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The actual flat setting of the train `tr` at viscosity `ν`, cell size `c = ν⁻²`, outward cutoff
profile `χ̂_o` and ring parameter `ε` (source 4557-4612). -/
def levelFlat {ν m : ℝ} [Fact (1 < m)] {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (hν : 0 < ν)
    (FI : FlatSettingInst.FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε : ℝ) :
    ConcreteYF.FlatSetting :=
  FlatSettingInst.actualFlatSetting (hc := ⟨cOf_pos hν⟩) FI χo ε

/-- **The pin of the per-level flat setting** (source 4557-4612): the flat setting of level `n` is
the actual flat setting of the level's train, `D.flat n = actualFlatSetting FI χ̂_o ε_n` for pinned
data `FI` (`FlatInstData`) of `D.train n` at `c_n = ν_n⁻²`. -/
def SeqData.IsActualFlat (D : SeqData) (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (m : ℝ)
    [Fact (1 < m)] (n : ℕ) : Prop :=
  ∃ FI : FlatSettingInst.FlatInstData κ (retNu D.Pl D.σ₀ n) (cOf (retNu D.Pl D.σ₀ n)) m (D.train n),
    D.flat n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)

/-- Under the pin, `𝔗_{μ,ν}` of the level is that of the actual flat setting. -/
theorem SeqData.IsActualFlat.frakT_eq {D : SeqData} {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    {m : ℝ} [Fact (1 < m)] {n : ℕ} (h : D.IsActualFlat κ m n) :
    ∃ FI : FlatSettingInst.FlatInstData κ (retNu D.Pl D.σ₀ n) (cOf (retNu D.Pl D.σ₀ n)) m (D.train n),
      ∀ (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), frakT (D.level n).flat ν μ χf A =
        frakT (levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)) ν μ χf A := by
  obtain ⟨FI, hFI⟩ := h
  exact ⟨FI, fun ν μ χf A => by rw [show (D.level n).flat = D.flat n from rfl, hFI]⟩

end UnforcedLeray.Short.PartIIIb.Concrete
