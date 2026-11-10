import LRX.PackedWordCertificate

namespace LRX.PackedSmall8.Block32
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def words : Array ℕ := #[8201095206365, 32911752919773, 197224217310, 3081628398, 197224217466, 788895489518, 32811257812445, 131647013354205, 788896870110, 12326513595, 788896869867, 3155581958075, 12326492027, 3081622907, 3081623006, 770405726, 12037589, 48150359, 196861589335, 787553810263, 3081628395, 770407098, 49215397333, 196888452565, 128504740573, 514246490845, 8499386832349, 197213940462, 12621763272149, 2124848949981, 2007886573, 8035101421, 126629047021, 49246862046, 101933051358, 2075061726, 33200922285, 769488366, 3150213737397, 802814618485, 12544830325, 192370158, 3077955054, 518764461, 769482222, 49223130606, 3149785918389, 33200925405, 8031546295, 32140405687, 506516188087, 196987449054, 787956494046, 8300246907, 514017582573, 2056984583661, 2052654069085, 50322976213, 2052704400733, 8210616282797, 12600854949591, 3220670438869, 132803689143, 3077953467, 769480635, 50179321303, 514018962910, 132803701623, 196892522427, 3077928891, 12311820219, 2075057847, 518748909, 12023262, 49222118325, 12303854517, 192277854, 3005790, 2074995639, 48093051, 196888473303, 49215418071, 769111419, 12023163, 787553417047, 196861196119, 196888354261, 49215299029, 770366933, 3081467735, 12017367, 187863, 769096629, 192248757, 3004341, 46965, 398175981, 8105709, 192370554, 6272415605, 25483262685, 518765277, 1592703927, 32422839, 769482219, 25089662423, 128504739757, 2075061111, 192372090, 6297581429, 48977781, 1566406517, 12544043893, 50176175575, 8224517772765, 132803124717, 197214959447, 49303739861, 3155437247957, 33200765661, 32897213627101, 8501742919405, 805167610590, 12580743918, 805167610746, 3152219453357, 131588501139165, 34006971677623, 3220670443230, 50322975675, 3220670442987, 12608877813431, 50322954107, 12580738427, 12580738526, 3145184606, 49143509, 196574039, 787446357463, 197013715895, 12580743915, 3145185978, 196861589365, 49253428973, 514018963165, 2056985964253, 3150188558253, 787419674541, 3149785905069, 531358906285, 128504740789, 33209933278, 49221696222, 12303432414, 49215404766, 8302482910, 769095150, 192592606, 49222089645, 12325926829, 192592813, 3009262, 768990702, 192396206, 192592762, 769089006, 49215404973, 12313357229, 514018963159, 132839733115, 196886785758, 49303747294, 196861619934, 49253428958, 2056075852663, 8227943857015, 12882681912670, 201291904885, 12599143620279, 2125435625143, 196888358583, 49303707319, 3076380603, 770371294, 12037051, 770371255, 196861619895, 49253428919, 3076356027, 770371051, 3075962811, 769584827, 12017118, 3003870, 769095597, 192247725, 3004254, 750942, 48068475, 12015483, 3076382391, 768990903, 12017019, 3003771, 12305529783, 3075963831, 3076382445, 768990957, 192241389, 769089261, 187767, 46935, 12017133, 3003885, 46941, 11733, 192247674, 32431573, 48060282, 192272250, 5869762397, 129726301, 768990699, 129726295, 192241131, 769089003, 23479049591, 518905207, 3009259, 192273786, 752314, 48977757, 192592621, 770370487, 196861619127, 33209933293, 49221696237, 12303432429, 49215404781, 8302482925, 128504395701, 514246145973, 8104258664373, 197228198743, 8210817603031, 2124647623389, 32126097333, 128561534901, 2124645381493, 750400689630, 1630925469150, 33197635038, 46933695966, 11733423582, 2124630896349, 751274653533, 11739166557, 182315758, 46671453678, 8299342773, 11739291093, 46957164381, 3005099112285, 33197371101, 2007881181, 8035096029, 126629041629, 49306056535, 128294025131, 504515384797, 501970269, 2008773981, 31657260381, 184379420126, 25483210206, 518712798, 8299339437, 2876960222, 531157702109, 2945993009885, 46031301341, 719239085, 6370801581, 129677229, 2880928685, 184379435741, 407731301085, 8299342557, 7843306, 31387114, 494644714, 25211416042, 6370450910, 129326558, 501970293, 2008774005, 31657260405, 1613530625397, 407708874206, 8276915678, 8277292922, 46031156702, 129677178, 719236574, 11238110, 391609054, 6370457054, 129332702, 1568111326, 45014510, 99543774, 2026206, 129687213, 45805022, 8299959773, 46890085085, 732818141, 11450285, 2026362, 11447774, 2074989941, 732673502, 6125038, 178910, 8299981749, 2931537374, 33199927005, 187617372893, 2931273437, 732818357, 2865845, 2798, 11463605, 45854429, 11463389, 179117, 99543981, 2026413, 732815021, 1568111533, 6370814685, 129690333, 1555374, 31662, 11450234, 24501742, 98483118, 32422581, 179066, 6118894, 11460269, 24600046, 2933829341, 733457333, 6370814901, 129690549, 46900161461, 100359138229, 25483259613, 518762205, 128504389335, 514246139607, 12600758073181, 201523379037, 788895587822, 132790540155, 514017582807, 2056984583895, 2052654069109, 49307049685, 2052704400757, 8498590493559, 788895489773, 201510009693, 196888328029, 3081623390, 48150365, 3081623021, 12599208802141, 132789484407, 196886755165, 49246854613, 196989115861, 33197371095, 2007881175, 8035096023, 126629041623, 12621763147613, 1630928614878, 33200780766, 31373227, 125548459, 1978578859, 187600645598, 25483259358, 518761950, 518764410, 2933829086, 33109171691, 187765077470, 1566437086, 45841118, 398175966, 8105694, 183426542, 6272446174, 25211678430, 517330811, 2007881079, 8035095927, 126629041527, 737517743582, 101932840827, 2074851195, 8031524727, 32140384119, 32072719850, 12326514133, 32073506282, 128290879418, 2050774457834, 788896865749, 33197357751, 11507840891, 3078272885, 196892866421, 128504389086, 33197370231, 737517742967, 11523714743, 25483206327, 518708919, 8105451, 45854174, 8299982517, 2934683102, 24500155, 716510, 518748855, 183220091, 33199839095, 128504739706, 2931272567, 45801143, 132799708023, 750469491575, 33199926999, 11726149499, 3081467741, 11725093751, 45853559, 716471, 183417719, 45854423, 11464373, 11195, 6221499, 126651, 45856634, 98006971, 393932475, 129691317, 398175927, 8105655, 2931260087, 6272446135, 2007886558, 518761335, 45841079, 98400187, 716267, 24475579, 2933829335, 11735317367, 128504395230, 2075048823, 401436552919, 197214959453, 25483259607, 518762199, 518962101, 182310366, 2075848413, 5869369181, 182310750, 45577566, 2075848407, 729241467, 8303393655, 23477476727, 729243003, 182310267, 531417193965, 186685815735, 132854282973, 46671453933, 11667857133, 46671552237, 11394423, 2848599, 729243117, 182310381, 2848605, 712149, 129739701, 366865333, 518958813, 1467461341, 392031157, 90041269, 32429429, 5748190, 31674, 89566, 21982, 95710, 2027181, 5732269, 129717725, 366865117, 6125485, 1406893, 686, 23902, 43949, 96094, 11251421, 2812853, 129740469, 22992763, 126699, 358267, 175838, 382843, 518958807, 1467461335, 2075835255, 5869845367, 1568124631, 360165079, 518870903, 2007886714, 8108727, 22929079, 5627575, 24501943, 45005687, 11251415, 384379, 175799, 2747, 95611, 8108781, 22929133, 518961885, 1467464413, 24501997, 11253677, 32435127, 91716535, 2075847543, 5869857655, 98007991, 45014711, 132853456365, 375670103533, 33213348573, 93917510365, 46672829909, 100359961309, 24600301, 703415, 1574419165, 720075485, 11254493, 175853, 85, 373, 349, 1501, 96181, 22453, 343, 1495, 1399, 6007, 384727, 89815, 89581, 384493, 21997, 95725, 5733085, 24607453, 24607669, 5733301, 98430685, 22933213, 6126517, 1407925, 6370802613, 129678261, 2931252693, 11725010781, 25483210461, 518713053, 25483210455, 518713047, 11725010775, 46900043127, 128504753077, 2074852215, 183334743, 733338999, 45833685, 183334749, 11733423597, 46933695981, 514019012317, 132437110493, 3001602760173, 750467774301, 3001877886813, 33197619933, 1592612789, 32331701, 5762427829, 25089780661, 6370457525, 129333173, 24884597, 505205, 6125434, 1406842, 388842, 7914, 1529722, 43898, 179809205, 719236829, 6150010, 2809517, 24884573, 505181, 90037933, 392027821, 99538397, 2020829, 99538391, 2020823, 24501739, 11253626, 1555371, 31659, 6370451159, 129326807, 23049711319, 126561990574, 32127153525, 517332695, 719236823, 2876947319, 6118891, 175595, 11238071, 24600043, 31373230, 8083319, 1978578862, 360151735, 99538295, 2020727, 710005, 698, 2862005, 11448029, 2840029, 44717, 2862773, 2795, 11448023, 45792119, 6151546, 178871, 45805271, 183221111, 11451317, 45805277, 2931522269, 11726151149, 45804407, 715703, 2930695661, 732658397, 11451101, 178925, 99543789, 2026221, 720232109, 1568111341, 6370802397, 129678045, 398175159, 8104887, 2880928439, 6272445367, 2007886765, 517332461, 44952503, 1574402797, 11238125, 719239901, 46031141597, 100761778909, 128508614109, 33109277405, 8104262882781, 2987061370325, 407708859101, 8276900573]
def table (c : PermCode 6) : List Letter := unpackWord words[codeIndex c]!

private theorem checked_first_0_0 : ∀ d : PermCode 4,
    eval (table ((0 : Fin 6),((0 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((0 : Fin 6),((0 : Fin 5),d)))) ∧ (table ((0 : Fin 6),((0 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_0_1 : ∀ d : PermCode 4,
    eval (table ((0 : Fin 6),((1 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((0 : Fin 6),((1 : Fin 5),d)))) ∧ (table ((0 : Fin 6),((1 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_0_2 : ∀ d : PermCode 4,
    eval (table ((0 : Fin 6),((2 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((0 : Fin 6),((2 : Fin 5),d)))) ∧ (table ((0 : Fin 6),((2 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_0_3 : ∀ d : PermCode 4,
    eval (table ((0 : Fin 6),((3 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((0 : Fin 6),((3 : Fin 5),d)))) ∧ (table ((0 : Fin 6),((3 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_0_4 : ∀ d : PermCode 4,
    eval (table ((0 : Fin 6),((4 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((0 : Fin 6),((4 : Fin 5),d)))) ∧ (table ((0 : Fin 6),((4 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_1_0 : ∀ d : PermCode 4,
    eval (table ((1 : Fin 6),((0 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((1 : Fin 6),((0 : Fin 5),d)))) ∧ (table ((1 : Fin 6),((0 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_1_1 : ∀ d : PermCode 4,
    eval (table ((1 : Fin 6),((1 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((1 : Fin 6),((1 : Fin 5),d)))) ∧ (table ((1 : Fin 6),((1 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_1_2 : ∀ d : PermCode 4,
    eval (table ((1 : Fin 6),((2 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((1 : Fin 6),((2 : Fin 5),d)))) ∧ (table ((1 : Fin 6),((2 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_1_3 : ∀ d : PermCode 4,
    eval (table ((1 : Fin 6),((3 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((1 : Fin 6),((3 : Fin 5),d)))) ∧ (table ((1 : Fin 6),((3 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_1_4 : ∀ d : PermCode 4,
    eval (table ((1 : Fin 6),((4 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((1 : Fin 6),((4 : Fin 5),d)))) ∧ (table ((1 : Fin 6),((4 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_2_0 : ∀ d : PermCode 4,
    eval (table ((2 : Fin 6),((0 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((2 : Fin 6),((0 : Fin 5),d)))) ∧ (table ((2 : Fin 6),((0 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_2_1 : ∀ d : PermCode 4,
    eval (table ((2 : Fin 6),((1 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((2 : Fin 6),((1 : Fin 5),d)))) ∧ (table ((2 : Fin 6),((1 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_2_2 : ∀ d : PermCode 4,
    eval (table ((2 : Fin 6),((2 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((2 : Fin 6),((2 : Fin 5),d)))) ∧ (table ((2 : Fin 6),((2 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_2_3 : ∀ d : PermCode 4,
    eval (table ((2 : Fin 6),((3 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((2 : Fin 6),((3 : Fin 5),d)))) ∧ (table ((2 : Fin 6),((3 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_2_4 : ∀ d : PermCode 4,
    eval (table ((2 : Fin 6),((4 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((2 : Fin 6),((4 : Fin 5),d)))) ∧ (table ((2 : Fin 6),((4 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_3_0 : ∀ d : PermCode 4,
    eval (table ((3 : Fin 6),((0 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((3 : Fin 6),((0 : Fin 5),d)))) ∧ (table ((3 : Fin 6),((0 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_3_1 : ∀ d : PermCode 4,
    eval (table ((3 : Fin 6),((1 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((3 : Fin 6),((1 : Fin 5),d)))) ∧ (table ((3 : Fin 6),((1 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_3_2 : ∀ d : PermCode 4,
    eval (table ((3 : Fin 6),((2 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((3 : Fin 6),((2 : Fin 5),d)))) ∧ (table ((3 : Fin 6),((2 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_3_3 : ∀ d : PermCode 4,
    eval (table ((3 : Fin 6),((3 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((3 : Fin 6),((3 : Fin 5),d)))) ∧ (table ((3 : Fin 6),((3 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_3_4 : ∀ d : PermCode 4,
    eval (table ((3 : Fin 6),((4 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((3 : Fin 6),((4 : Fin 5),d)))) ∧ (table ((3 : Fin 6),((4 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_4_0 : ∀ d : PermCode 4,
    eval (table ((4 : Fin 6),((0 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((4 : Fin 6),((0 : Fin 5),d)))) ∧ (table ((4 : Fin 6),((0 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_4_1 : ∀ d : PermCode 4,
    eval (table ((4 : Fin 6),((1 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((4 : Fin 6),((1 : Fin 5),d)))) ∧ (table ((4 : Fin 6),((1 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_4_2 : ∀ d : PermCode 4,
    eval (table ((4 : Fin 6),((2 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((4 : Fin 6),((2 : Fin 5),d)))) ∧ (table ((4 : Fin 6),((2 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_4_3 : ∀ d : PermCode 4,
    eval (table ((4 : Fin 6),((3 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((4 : Fin 6),((3 : Fin 5),d)))) ∧ (table ((4 : Fin 6),((3 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_4_4 : ∀ d : PermCode 4,
    eval (table ((4 : Fin 6),((4 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((4 : Fin 6),((4 : Fin 5),d)))) ∧ (table ((4 : Fin 6),((4 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_5_0 : ∀ d : PermCode 4,
    eval (table ((5 : Fin 6),((0 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((5 : Fin 6),((0 : Fin 5),d)))) ∧ (table ((5 : Fin 6),((0 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_5_1 : ∀ d : PermCode 4,
    eval (table ((5 : Fin 6),((1 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((5 : Fin 6),((1 : Fin 5),d)))) ∧ (table ((5 : Fin 6),((1 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_5_2 : ∀ d : PermCode 4,
    eval (table ((5 : Fin 6),((2 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((5 : Fin 6),((2 : Fin 5),d)))) ∧ (table ((5 : Fin 6),((2 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_5_3 : ∀ d : PermCode 4,
    eval (table ((5 : Fin 6),((3 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((5 : Fin 6),((3 : Fin 5),d)))) ∧ (table ((5 : Fin 6),((3 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

private theorem checked_first_5_4 : ∀ d : PermCode 4,
    eval (table ((5 : Fin 6),((4 : Fin 5),d)))=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), ((5 : Fin 6),((4 : Fin 5),d)))) ∧ (table ((5 : Fin 6),((4 : Fin 5),d))).length ≤ Nat.choose 8 2 := by
  decide +kernel

theorem checked : ∀ c : PermCode 6,
    eval (table c)=decode (n := 8) ((⟨4,by decide⟩ : Fin 8), ((⟨4,by decide⟩ : Fin 7), c)) ∧ (table c).length ≤ Nat.choose 8 2 := by
  rintro ⟨i0, i1, c⟩
  fin_cases i0 <;> fin_cases i1
  · exact checked_first_0_0 c
  · exact checked_first_0_1 c
  · exact checked_first_0_2 c
  · exact checked_first_0_3 c
  · exact checked_first_0_4 c
  · exact checked_first_1_0 c
  · exact checked_first_1_1 c
  · exact checked_first_1_2 c
  · exact checked_first_1_3 c
  · exact checked_first_1_4 c
  · exact checked_first_2_0 c
  · exact checked_first_2_1 c
  · exact checked_first_2_2 c
  · exact checked_first_2_3 c
  · exact checked_first_2_4 c
  · exact checked_first_3_0 c
  · exact checked_first_3_1 c
  · exact checked_first_3_2 c
  · exact checked_first_3_3 c
  · exact checked_first_3_4 c
  · exact checked_first_4_0 c
  · exact checked_first_4_1 c
  · exact checked_first_4_2 c
  · exact checked_first_4_3 c
  · exact checked_first_4_4 c
  · exact checked_first_5_0 c
  · exact checked_first_5_1 c
  · exact checked_first_5_2 c
  · exact checked_first_5_3 c
  · exact checked_first_5_4 c

#print axioms checked
end LRX.PackedSmall8.Block32
