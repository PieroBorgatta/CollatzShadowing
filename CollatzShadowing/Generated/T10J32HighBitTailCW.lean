import CollatzShadowing.Generated.T10J32HighBitTailCWRows00
import CollatzShadowing.Generated.T10J32HighBitTailCWRows01
import CollatzShadowing.Generated.T10J32HighBitTailCWRows02
import CollatzShadowing.Generated.T10J32HighBitTailCWRows03
import CollatzShadowing.Generated.T10J32HighBitTailCWRows04
import CollatzShadowing.Generated.T10J32HighBitTailCWRows05
import CollatzShadowing.Generated.T10J32HighBitTailCWRows06
import CollatzShadowing.Generated.T10J32HighBitTailCWRows07
import CollatzShadowing.Generated.T10J32HighBitTailCWRows08
import CollatzShadowing.Generated.T10J32HighBitTailCWRows09
import CollatzShadowing.Generated.T10J32HighBitTailCWRows10
import CollatzShadowing.Generated.T10J32HighBitTailCWRows11
import CollatzShadowing.Generated.T10J32HighBitTailCWRows12
import CollatzShadowing.Generated.T10J32HighBitTailCWRows13

set_option linter.style.longLine false
set_option linter.style.cdot false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- Generated evaluated row witnesses for the `T = 10`, `j = 32` matrix. -/
noncomputable def t10j32HighBitTailEvaluatedRows :
    ∀ i, EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal i := by
  intro i
  rcases i with ⟨n, hn⟩
  interval_cases n
  · exact t10j32HighBitTailNode000Evaluated
  · exact t10j32HighBitTailNode001Evaluated
  · exact t10j32HighBitTailNode002Evaluated
  · exact t10j32HighBitTailNode003Evaluated
  · exact t10j32HighBitTailNode004Evaluated
  · exact t10j32HighBitTailNode005Evaluated
  · exact t10j32HighBitTailNode006Evaluated
  · exact t10j32HighBitTailNode007Evaluated
  · exact t10j32HighBitTailNode008Evaluated
  · exact t10j32HighBitTailNode009Evaluated
  · exact t10j32HighBitTailNode010Evaluated
  · exact t10j32HighBitTailNode011Evaluated
  · exact t10j32HighBitTailNode012Evaluated
  · exact t10j32HighBitTailNode013Evaluated
  · exact t10j32HighBitTailNode014Evaluated
  · exact t10j32HighBitTailNode015Evaluated
  · exact t10j32HighBitTailNode016Evaluated
  · exact t10j32HighBitTailNode017Evaluated
  · exact t10j32HighBitTailNode018Evaluated
  · exact t10j32HighBitTailNode019Evaluated
  · exact t10j32HighBitTailNode020Evaluated
  · exact t10j32HighBitTailNode021Evaluated
  · exact t10j32HighBitTailNode022Evaluated
  · exact t10j32HighBitTailNode023Evaluated
  · exact t10j32HighBitTailNode024Evaluated
  · exact t10j32HighBitTailNode025Evaluated
  · exact t10j32HighBitTailNode026Evaluated
  · exact t10j32HighBitTailNode027Evaluated
  · exact t10j32HighBitTailNode028Evaluated
  · exact t10j32HighBitTailNode029Evaluated
  · exact t10j32HighBitTailNode030Evaluated
  · exact t10j32HighBitTailNode031Evaluated
  · exact t10j32HighBitTailNode032Evaluated
  · exact t10j32HighBitTailNode033Evaluated
  · exact t10j32HighBitTailNode034Evaluated
  · exact t10j32HighBitTailNode035Evaluated
  · exact t10j32HighBitTailNode036Evaluated
  · exact t10j32HighBitTailNode037Evaluated
  · exact t10j32HighBitTailNode038Evaluated
  · exact t10j32HighBitTailNode039Evaluated
  · exact t10j32HighBitTailNode040Evaluated
  · exact t10j32HighBitTailNode041Evaluated
  · exact t10j32HighBitTailNode042Evaluated
  · exact t10j32HighBitTailNode043Evaluated
  · exact t10j32HighBitTailNode044Evaluated
  · exact t10j32HighBitTailNode045Evaluated
  · exact t10j32HighBitTailNode046Evaluated
  · exact t10j32HighBitTailNode047Evaluated
  · exact t10j32HighBitTailNode048Evaluated
  · exact t10j32HighBitTailNode049Evaluated
  · exact t10j32HighBitTailNode050Evaluated
  · exact t10j32HighBitTailNode051Evaluated
  · exact t10j32HighBitTailNode052Evaluated
  · exact t10j32HighBitTailNode053Evaluated
  · exact t10j32HighBitTailNode054Evaluated
  · exact t10j32HighBitTailNode055Evaluated
  · exact t10j32HighBitTailNode056Evaluated
  · exact t10j32HighBitTailNode057Evaluated
  · exact t10j32HighBitTailNode058Evaluated
  · exact t10j32HighBitTailNode059Evaluated
  · exact t10j32HighBitTailNode060Evaluated
  · exact t10j32HighBitTailNode061Evaluated
  · exact t10j32HighBitTailNode062Evaluated
  · exact t10j32HighBitTailNode063Evaluated
  · exact t10j32HighBitTailNode064Evaluated
  · exact t10j32HighBitTailNode065Evaluated
  · exact t10j32HighBitTailNode066Evaluated
  · exact t10j32HighBitTailNode067Evaluated
  · exact t10j32HighBitTailNode068Evaluated
  · exact t10j32HighBitTailNode069Evaluated
  · exact t10j32HighBitTailNode070Evaluated
  · exact t10j32HighBitTailNode071Evaluated
  · exact t10j32HighBitTailNode072Evaluated
  · exact t10j32HighBitTailNode073Evaluated
  · exact t10j32HighBitTailNode074Evaluated
  · exact t10j32HighBitTailNode075Evaluated
  · exact t10j32HighBitTailNode076Evaluated
  · exact t10j32HighBitTailNode077Evaluated
  · exact t10j32HighBitTailNode078Evaluated
  · exact t10j32HighBitTailNode079Evaluated
  · exact t10j32HighBitTailNode080Evaluated
  · exact t10j32HighBitTailNode081Evaluated
  · exact t10j32HighBitTailNode082Evaluated
  · exact t10j32HighBitTailNode083Evaluated
  · exact t10j32HighBitTailNode084Evaluated
  · exact t10j32HighBitTailNode085Evaluated
  · exact t10j32HighBitTailNode086Evaluated
  · exact t10j32HighBitTailNode087Evaluated
  · exact t10j32HighBitTailNode088Evaluated
  · exact t10j32HighBitTailNode089Evaluated
  · exact t10j32HighBitTailNode090Evaluated
  · exact t10j32HighBitTailNode091Evaluated
  · exact t10j32HighBitTailNode092Evaluated
  · exact t10j32HighBitTailNode093Evaluated
  · exact t10j32HighBitTailNode094Evaluated
  · exact t10j32HighBitTailNode095Evaluated
  · exact t10j32HighBitTailNode096Evaluated
  · exact t10j32HighBitTailNode097Evaluated
  · exact t10j32HighBitTailNode098Evaluated
  · exact t10j32HighBitTailNode099Evaluated
  · exact t10j32HighBitTailNode100Evaluated
  · exact t10j32HighBitTailNode101Evaluated
  · exact t10j32HighBitTailNode102Evaluated
  · exact t10j32HighBitTailNode103Evaluated
  · exact t10j32HighBitTailNode104Evaluated
  · exact t10j32HighBitTailNode105Evaluated
  · exact t10j32HighBitTailNode106Evaluated
  · exact t10j32HighBitTailNode107Evaluated
  · exact t10j32HighBitTailNode108Evaluated
  · exact t10j32HighBitTailNode109Evaluated
  · exact t10j32HighBitTailNode110Evaluated
  · exact t10j32HighBitTailNode111Evaluated
  · exact t10j32HighBitTailNode112Evaluated
  · exact t10j32HighBitTailNode113Evaluated
  · exact t10j32HighBitTailNode114Evaluated
  · exact t10j32HighBitTailNode115Evaluated
  · exact t10j32HighBitTailNode116Evaluated
  · exact t10j32HighBitTailNode117Evaluated
  · exact t10j32HighBitTailNode118Evaluated
  · exact t10j32HighBitTailNode119Evaluated
  · exact t10j32HighBitTailNode120Evaluated
  · exact t10j32HighBitTailNode121Evaluated
  · exact t10j32HighBitTailNode122Evaluated
  · exact t10j32HighBitTailNode123Evaluated
  · exact t10j32HighBitTailNode124Evaluated
  · exact t10j32HighBitTailNode125Evaluated
  · exact t10j32HighBitTailNode126Evaluated
  · exact t10j32HighBitTailNode127Evaluated
  · exact t10j32HighBitTailNode128Evaluated
  · exact t10j32HighBitTailNode129Evaluated
  · exact t10j32HighBitTailNode130Evaluated
  · exact t10j32HighBitTailNode131Evaluated
  · exact t10j32HighBitTailNode132Evaluated
  · exact t10j32HighBitTailNode133Evaluated
  · exact t10j32HighBitTailNode134Evaluated
  · exact t10j32HighBitTailNode135Evaluated
  · exact t10j32HighBitTailNode136Evaluated
  · exact t10j32HighBitTailNode137Evaluated
  · exact t10j32HighBitTailNode138Evaluated
  · exact t10j32HighBitTailNode139Evaluated
  · exact t10j32HighBitTailNode140Evaluated
  · exact t10j32HighBitTailNode141Evaluated
  · exact t10j32HighBitTailNode142Evaluated
  · exact t10j32HighBitTailNode143Evaluated
  · exact t10j32HighBitTailNode144Evaluated
  · exact t10j32HighBitTailNode145Evaluated
  · exact t10j32HighBitTailNode146Evaluated
  · exact t10j32HighBitTailNode147Evaluated
  · exact t10j32HighBitTailNode148Evaluated
  · exact t10j32HighBitTailNode149Evaluated
  · exact t10j32HighBitTailNode150Evaluated
  · exact t10j32HighBitTailNode151Evaluated
  · exact t10j32HighBitTailNode152Evaluated
  · exact t10j32HighBitTailNode153Evaluated
  · exact t10j32HighBitTailNode154Evaluated
  · exact t10j32HighBitTailNode155Evaluated
  · exact t10j32HighBitTailNode156Evaluated
  · exact t10j32HighBitTailNode157Evaluated
  · exact t10j32HighBitTailNode158Evaluated
  · exact t10j32HighBitTailNode159Evaluated
  · exact t10j32HighBitTailNode160Evaluated
  · exact t10j32HighBitTailNode161Evaluated
  · exact t10j32HighBitTailNode162Evaluated
  · exact t10j32HighBitTailNode163Evaluated
  · exact t10j32HighBitTailNode164Evaluated
  · exact t10j32HighBitTailNode165Evaluated
  · exact t10j32HighBitTailNode166Evaluated
  · exact t10j32HighBitTailNode167Evaluated
  · exact t10j32HighBitTailNode168Evaluated
  · exact t10j32HighBitTailNode169Evaluated
  · exact t10j32HighBitTailNode170Evaluated
  · exact t10j32HighBitTailNode171Evaluated
  · exact t10j32HighBitTailNode172Evaluated
  · exact t10j32HighBitTailNode173Evaluated
  · exact t10j32HighBitTailNode174Evaluated
  · exact t10j32HighBitTailNode175Evaluated
  · exact t10j32HighBitTailNode176Evaluated
  · exact t10j32HighBitTailNode177Evaluated
  · exact t10j32HighBitTailNode178Evaluated
  · exact t10j32HighBitTailNode179Evaluated
  · exact t10j32HighBitTailNode180Evaluated
  · exact t10j32HighBitTailNode181Evaluated
  · exact t10j32HighBitTailNode182Evaluated
  · exact t10j32HighBitTailNode183Evaluated
  · exact t10j32HighBitTailNode184Evaluated
  · exact t10j32HighBitTailNode185Evaluated
  · exact t10j32HighBitTailNode186Evaluated
  · exact t10j32HighBitTailNode187Evaluated
  · exact t10j32HighBitTailNode188Evaluated
  · exact t10j32HighBitTailNode189Evaluated
  · exact t10j32HighBitTailNode190Evaluated
  · exact t10j32HighBitTailNode191Evaluated
  · exact t10j32HighBitTailNode192Evaluated
  · exact t10j32HighBitTailNode193Evaluated
  · exact t10j32HighBitTailNode194Evaluated
  · exact t10j32HighBitTailNode195Evaluated
  · exact t10j32HighBitTailNode196Evaluated
  · exact t10j32HighBitTailNode197Evaluated
  · exact t10j32HighBitTailNode198Evaluated
  · exact t10j32HighBitTailNode199Evaluated
  · exact t10j32HighBitTailNode200Evaluated
  · exact t10j32HighBitTailNode201Evaluated
  · exact t10j32HighBitTailNode202Evaluated
  · exact t10j32HighBitTailNode203Evaluated
  · exact t10j32HighBitTailNode204Evaluated
  · exact t10j32HighBitTailNode205Evaluated
  · exact t10j32HighBitTailNode206Evaluated
  · exact t10j32HighBitTailNode207Evaluated
  · exact t10j32HighBitTailNode208Evaluated
  · exact t10j32HighBitTailNode209Evaluated
  · exact t10j32HighBitTailNode210Evaluated
  · exact t10j32HighBitTailNode211Evaluated
  · exact t10j32HighBitTailNode212Evaluated
  · exact t10j32HighBitTailNode213Evaluated
  · exact t10j32HighBitTailNode214Evaluated
  · exact t10j32HighBitTailNode215Evaluated
  · exact t10j32HighBitTailNode216Evaluated
  · exact t10j32HighBitTailNode217Evaluated
  · exact t10j32HighBitTailNode218Evaluated
  · exact t10j32HighBitTailNode219Evaluated
  · exact t10j32HighBitTailNode220Evaluated
  · exact t10j32HighBitTailNode221Evaluated
  · exact t10j32HighBitTailNode222Evaluated
  · exact t10j32HighBitTailNode223Evaluated

/-- Full generated finite Collatz-Wielandt certificate for the `T = 10`, `j = 32` matrix. -/
theorem t10j32HighBitTailFiniteCWCertificate :
    FiniteCWCertificate t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal :=
  finiteCWCertificateOfEvaluatedRows t10j32HighBitTailEvaluatedRows

/-- Spectral-radius bound for the generated `T = 10`, `j = 32` matrix. -/
theorem t10j32HighBitTailSpectralRadiusBound :
    spectralRadius ℝ (nnrealMatrixToReal t10j32HighBitTailMatrix) ≤
      (t10j32HighBitTailAlphaNNReal : ℝ≥0∞) :=
  spectralRadius_le_of_finiteCWCertificate
    t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
    t10j32HighBitTailAlphaNNReal t10j32HighBitTailFiniteCWCertificate

/-- The same bound stated with the literal rational `97/2000`. -/
theorem t10j32HighBitTailSpectralRadiusBound_97_2000 :
    spectralRadius ℝ (nnrealMatrixToReal t10j32HighBitTailMatrix) ≤
      (((97 : NNReal) / (2000 : NNReal)) : ℝ≥0∞) := by
  simpa [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
    ProbabilityEntry.toNNReal] using t10j32HighBitTailSpectralRadiusBound

end Generated
end CollatzShadowing
