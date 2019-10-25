$[ set.mm $]

$(

  Add to #bib section of mmset.raw.html :

  <LI><A NAME="Dence1983"></A> [Dence1983] Thomas P. Dence, <I>Solving
  Math Problems in B.A.S.I.C.</I>, TAB Books, Blue Ridge Summit,
  PA. (1983) QA76.95 D46;</LI>

$)

$(
  MSC Classification 11A63 ( and 11A51 )
$)

$(
                             ~~ PUBLIC DOMAIN ~~
  This work is waived of all rights, including copyright, according to the CC0
  Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Richard Penner
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
     Number Theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Anomalous Cancellation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Proper cancellation is reducing the magnitude of numerators and
  denominators by cancelling common non-zero factors.  Example:
  ` |- ( ( 1 x. 6 ) / ( 6 x. 4 ) ) = ( 1 / 4 ) ` . See ~ divcan5 .

  Since multiplication by 10 (in base 10) is the same as a positional
  shift by adding a zero the the right, proper cancellation by
  removing common powers of 10 is equivalent to removing the same
  number of zeros on the right.  Example:
  ` |- ( ( ; 1 0 ) / ( ; 4 0 ) ) = ( 1 / 4 ) ` . See ~ dec0u .

  Anomolous Cancellation is the faulty mathematical procedure of
  removing identical digits from numerator and denominator to in
  the event when the result in an equivalent fraction. Example:
  ` |- ( ; 1 6 / ; 6 4 ) = ( 1 / 4 ) ` .

  In this subsection, the theorems work on the non-degenerate
  two-digit case in arbitrary base, ` B ` . Thus ` T ` is reserved
  for the "tens" digit and ` U ` is the "units" digit. ` W ` was
  chosen to represent the common digit which is targetted by the
  improper procedure. We always represent a two digit number as
  ` ( ( B x. T ) + U ) ` so that we may easily leverage the decimal
  operator for the ` B = 10 ` case.
$)

  $( Proper cancellation when common factor multiplies from the front.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan3 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                         -> ( ( B x. A ) / ( B x. C ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul co cdiv wceq simpl1 simp3 simpr anim12i simp2
    simpl 3jca divcan5 syl ) ADEZBDEZCDEZFZBGHZCGHZIZIZUCUEUHIZUDUGIZFBAJKBCJKL
    KACLKMUJUCUKULUCUDUEUINUFUEUIUHUCUDUEOUGUHPQUFUDUIUGUCUDUERUGUHSQTACBUAUB
    $.

  $( Proper cancellation when common factor is in the interior.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan1 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                         -> ( ( A x. B ) / ( B x. C ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul cdiv wceq rp-propercan3 simpl2 simpl1 mulcomd
    co oveq1d eqeq1d mpbid ) ADEZBDEZCDEZFBGHCGHIZIZBAJQZBCJQZKQZACKQZLABJQZUGK
    QZUILABCMUEUHUKUIUEUFUJUGKUEBAUAUBUCUDNUAUBUCUDOPRST $.

  $( Proper cancellation when common factor is last.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan2 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                        -> ( ( A x. B ) / ( C x. B ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul cdiv wceq rp-propercan1 simpl2 simpl3 mulcomd
    co oveq2d eqeq1d mpbid ) ADEZBDEZCDEZFBGHCGHIZIZABJQZBCJQZKQZACKQZLUFCBJQZK
    QZUILABCMUEUHUKUIUEUGUJUFKUEBCUAUBUCUDNUAUBUCUDOPRST $.

  $( Proper cancellation when common factor is on exterior.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan4 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                        -> ( ( B x. A ) / ( C x. B ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul cdiv wceq rp-propercan3 simpl2 simpl3 mulcomd
    co oveq2d eqeq1d mpbid ) ADEZBDEZCDEZFBGHCGHIZIZBAJQZBCJQZKQZACKQZLUFCBJQZK
    QZUILABCMUEUHUKUIUEUGUJUFKUEBCUAUBUCUDNUAUBUCUDOPRST $.

  $( Proper cancellation when common factor is 10 and we use the decimal
     operator to represent two-digit terms.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan5 $p |- ( ( A e. CC /\ C e. CC /\ C =/= 0 )
                        -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
    ( cc wcel cc0 wne w3a c10 wa cdc cdiv wceq a1i jca cmul caddc df-dec mulcld
    co addid1d simp1 10nn0 nn0cni simp2 10pos gtneii simp3 rp-propercan3 simpl2
    3jca 0re simpl1 eqtr2d simpl3 oveq12d eqeq1d mpbid syl ) ACDZBCDZBEFZGZUSHC
    DZUTGZHEFZVAIZIZAEJZBEJZKSZABKSZLZVBVDVFVBUSVCUTUSUTVAUAVCVBHUBUCMUSUTVAUDU
    JVBVEVAVEVBEHUKUEUFMUSUTVAUGNNVGHAOSZHBOSZKSZVKLVLAHBUHVGVOVJVKVGVMVHVNVIKV
    GVHVMEPSZVMVHVPLVGAEQMVGVMVGHAUSVCUTVFUIZUSVCUTVFULRTUMVGVIVNEPSZVNVIVRLVGB
    EQMVGVNVGHBVQUSVCUTVFUNRTUMUOUPUQUR $.

  $( Proper cancellation when common factor is 10 and we use the decimal
     operator to represent two-digit terms.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan6 $p |- ( ( A e. NN0 /\ C e. NN )
                        -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
    ( cn0 wcel cn wa cc cc0 wne w3a cdiv co wceq nn0cn adantr nncn adantl nnne0
    cdc 3jca rp-propercan5 syl ) ACDZBEDZFZAGDZBGDZBHIZJAHSBHSKLABKLMUEUFUGUHUC
    UFUDANOUDUGUCBPQUDUHUCBRQTABUAUB $.

  $( "We all know that 9/12 is equivalent to 3/4". -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex1 $p |- ( 9 / ; 1 2 ) = ( 3 / 4 ) $=
    ( c9 c1 c2 cdc cdiv co c3 cmul c4 3t3e9 eqcomi 4t3e12 oveq12i cc cc0 wne wa
    wcel 3cn pm3.2i w3a wceq 4cn 3pm3.2i 3ne0 4ne0 rp-propercan4 ax-mp eqtri )
    ABCDZEFGGHFZIGHFZEFZGIEFZAUKUJULEUKAJKULUJLKMGNRZUOINRZUAZGOPZIOPZQZQUMUNUB
    UQUTUOUOUPSSUCUDURUSUEUFTTGGIUGUHUI $.

  $( "We all know ... that 21/56 is equivalent to 3/8." -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex2 $p |- ( ; 2 1 / ; 5 6 ) = ( 3 / 8 ) $=
    ( c2 c1 cdc c5 c6 cdiv co c7 c3 cmul c8 7t3e21 eqcomi cc wcel cc0 wa nnne0i
    wne pm3.2i oveq12i w3a wceq 3cn 7cn 8cn 3pm3.2i 7nn 8nn rp-propercan4 ax-mp
    8t7e56 eqtri ) ABCZDECZFGHIJGZKHJGZFGZIKFGZUNUPUOUQFUPUNLMUQUOULMUAINOZHNOZ
    KNOZUBZHPSZKPSZQZQURUSUCVCVFUTVAVBUDUEUFUGVDVEHUHRKUIRTTIHKUJUKUM $.

  $( "It is somewhat interesting to note that 16/64 is equal to 1/4". -Thomas
     P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex3 $p |- ( ; 1 6 / ; 6 4 ) = ( 1 / 4 ) $=
    ( c1 c6 c4 cdiv co cmul c8 cc wcel 8cn 8p8e16 ax-mp eqcomi c2 eqtri 4cn cc0
    cr 8re clt cdc caddc addcli eleq1i biimpi mulid2i 2timesi 2cn mulassi 4p4e8
    oveq2i mulcomi oveq1i 3eqtri 8t8e64 oveq12i w3a wne wa wceq ax-1cn readdcli
    3pm3.2i eleq1a wbr 8pos addgt0ii breq2i gt0ne0ii 4ne0 pm3.2i rp-propercan2
    wi ) ABUAZBCUAZDEAVNFEZCVNFEZDEZACDEZVNVPVOVQDVPVNVNGGUBEZHIZVNHIZGGJJUCWAW
    BVTVNHKUDUELZUFMVQVOVQGGFEZVOVQCNGFEZFEZCNFEZGFEZWDVNWECFWEVNWEVTVNGJUGKOMU
    KWHWFCNGPUHJUIMWGGGFWGNCFEZGCNPUHULWICCUBEGCPUGUJOOUMUNUOOMUPAHIZWBCHIZUQZV
    NQURZCQURZUSZUSVRVSUTWLWOWJWBWKVAWCPVCWMWNVNVNVTUTZVNRIZVTVNKMVTRIWPWQVMGGS
    SVBVTRVNVDLLQVTTVEZQVNTVEZGGSSVFVFVGWRWSVTVNQTKVHUELVIVJVKVKAVNCVLLO $.

  $( "The fraction 19/95 is equal to 1/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex4 $p |- ( ; 1 9 / ; 9 5 ) = ( 1 / 5 ) $=
    ( c1 c9 cdc c5 cdiv co cmul c10 caddc cc df-dec mulcli ax-mp eqcomi 5cn cc0
    wcel c4 eqtri oveq12i wceq wi 10nn0 nn0cni ax-1cn 9cn addcli eleq1a mulid2i
    oveq2i adddii mulid1i mulcomi addid1i 9t5e45 0cn 4cn add42i 5p4e9 3eqtri wa
    w3a wne 3pm3.2i 10re 1re remulcli 9re readdcli clt 10pos 0lt1 mulgt0ii 9pos
    cr wbr addgt0ii breq2i biimpi gt0ne0ii 5re 5pos pm3.2i rp-propercan2 ) ABCZ
    BDCZEFAWEGFZDWEGFZEFZADEFZWEWGWFWHEWGWEWEWEHAGFZBIFZUAZWEJQZABKZWLJQWMWNUBW
    KBHAHUCUDZUELZUFUGWLJWEUHMMZUINWHWFWHDWLGFDWKGFZDBGFZIFZWFWEWLDGWOUJDWKBOWQ
    UFUKXADPCZRDCZIFHDGFZPIFZHRGFZDIFZIFZWFWSXBWTXCIWSXEXBWSXDXEWSDHGFXDWKHDGHW
    PULUJDHOWPUMSXEXDXDHDWPOLZUNNSXBXEDPKZNSWTBDGFXCDBOUFUMUOSTXBXEXCXGIXJRDKTX
    HXDXFIFZDPIFZIFZWFXDPXFDXIUPHRWPUQLOURXMHBGFZDIFZWFXKXNXLDIXKHDRIFZGFZXNXQX
    KHDRWPOUQUKNXPBHGUSUJSDOUNTWFXOBDKNSSUTUTNTAJQZWNDJQZVBZWEPVCZDPVCZVAZVAWIW
    JUAXTYCXRWNXSUEWROVDYAYBWEWMWEVOQZWOWLVOQWMYDUBWKBHAVEVFVGZVHVIWLVOWEUHMMPW
    LVJVPZPWEVJVPZWKBYEVHHAVEVFVKVLVMVNVQYFYGWLWEPVJWEWLWONVRVSMVTDWAWBVTWCWCAW
    EDWDMS $.

  $( "Also 26/65 equals to 2/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 40.

     (Contributed by Richard Penner, 24-Oct-2019.) $)
  rp-propercanex5 $p |- ( ; 2 6 / ; 6 5 ) = ( 2 / 5 ) $=
    ( c2 c6 cdc c5 cdiv co c1 c3 cmul c10 2cn mulcomi 3cn eqcomi oveq12i oveq2i
    caddc 3eqtri 5cn ax-1cn df-dec 10nn0 nn0cni 3t2e6 adddii eqtr4i dec10p df-6
    eqtri 6cn oveq1i adddiri mulid1i mulcli addassi mulid2i 5t2e10 2p1e3 cc w3a
    wcel cc0 wne wa wceq cr 10re 3re readdcli eqeltrri recni 3pm3.2i 10pos 3pos
    clt addgt0ii breqtri gt0ne0ii 5nn nnne0i pm3.2i rp-propercan2 mp2an ) ABCZB
    DCZEFAGHCZIFZDWFIFZEFZADEFZWDWGWEWHEWDJAIFZBQFZAJHQFZIFZWGABUAWLAJIFZAHIFZQ
    FWNWKWOBWPQJAJUBUCZKLWPBWPHAIFBAHKMLUDUINOAJHKWQMUEUFWMWFAIHUGZPRWEJBIFZDQF
    ZDWMIFZWHBDUAWTDJIFZDAGQFZIFZQFZXBDHIFZQFZXAWTXBGJIFZQFZDGIFZQFXBXHXJQFZQFX
    EWSXIDXJQWSBJIFDGQFZJIFXIJBWQUJLBXLJIUHUKDGJSTWQULRXJDDSUMNOXBXHXJDJSWQUNGJ
    TWQUNDGSTUNUOXKXDXBQXKDAIFZXJQFXDXHXMXJQXHJXMJWQUPUQUFUKDAGSKTUEUFPRXDXFXBQ
    XCHDIURPPXAXGDJHSWQMUENRWMWFDIWRPROAUSVAZWFUSVAZDUSVAZUTWFVBVCZDVBVCZVDWIWJ
    VEXNXOXPKWFWMWFVFWRJHVGVHVIVJZVKSVLXQXRWFXSVBWMWFVOJHVGVHVMVNVPWRVQVRDVSVTW
    AAWFDWBWCUI $.

  $( "484/847 = 4/7". -Thomas P. Dence.

     Statement of [Dence1983] p. 40.

     (Contributed by Richard Penner, 24-Oct-2019.) $)
  rp-propercanex6 $p |- ( ; ; 4 8 4 / ; ; 8 4 7 ) = ( 4 / 7 ) $=
    ( c4 c8 cdc c7 co c1 c2 cmul c10 caddc df-dec 4cn 10re recni mulassi eqcomi
    oveq12i oveq2i 3eqtri 7cn ax-1cn 4t2e8 mulcomi mulcli mulid1i eqtr4i oveq1i
    cdiv 1re remulcli 2cn adddii 3eqtr4i 2re readdcli eqeltri eqtri 7t2e14 df-8
    cr addassi dec10p cc wcel w3a cc0 wne wceq 3pm3.2i 10pos 0lt1 mulgt0ii 2pos
    wa clt addgt0ii breqtrri gt0ne0ii 7re 7pos pm3.2i rp-propercan2 mp2an ) ABC
    ZACZBACZDCZUHEAFGCZFCZHEZDWIHEZUHEZADUHEZWEWJWGWKUHIWDHEZAJEAIWHHEZHEZAFHEZ
    JEZWEWJWNWPAWQJWNIAHEZWHHEZAIHEZWHHEWPWNIAWHHEZHEWTWDXBIHWDWSBJEZAIFHEZGJEZ
    HEZXBABKXAFHEZBJEAXDHEZAGHEZJEXCXFXGXHBXIJAIFLIMNZUAOXIBUBPQWSXGBJWSXAXGIAX
    JLUCZXAAILXJUDUEUFUGAXDGLXDIFMUIUJZNZUKULUMXEWHAHWHXEFGKZPZRSRIAWHXJLWHWHXE
    UTXNXDGXLUNUOUPZNZOUFWSXAWHHXKUGAIWHLXJXQOSWQAALUEPQWDAKWJAWOFJEZHEWRWIXRAH
    WHFKZRAWOFLWOIWHMXPUJZNZUAULUQUMIWFHEZDJEDWOHEZDFHEZJEZWGWKYBYCDYDJYBIDHEZW
    HHEZDIHEZWHHEYCYBIDWHHEZHEYGWFYIIHWFIBHEZAJEZDXEHEZYIBAKYHFHEZFACZJEZDXDHEZ
    DGHEZJEYKYLYMYPYNYQJDIFTXJUAOYQYNURPQYKYHIJEZAJEYHIAJEZJEYOYJYRAJYJIDFJEZHE
    YFXDJEYRBYTIHUSRIDFXJTUAULYFYHXDIJIDXJTUCZIXJUEQSUGYHIADITXJUDZXJLVAYHYMYSY
    NJYMYHYHUUBUEPAVBQSDXDGTXMUKULUMXEWHDHXORSRIDWHXJTXQOUFYFYHWHHUUAUGDIWHTXJX
    QOSYDDDTUEPQWFDKWKDXRHEYEWIXRDHXSRDWOFTYAUAULUQUMQAVCVDZWIVCVDZDVCVDZVEWIVF
    VGZDVFVGZVNWLWMVHUUCUUDUUELWIWIXRUTXSWOFXTUIUOUPZNTVIUUFUUGWIUUHVFXRWIVOWOF
    XTUIIWHMXPVJVFXEWHVOXDGXLUNIFMUIVJVKVLVMVPXNVQVLVKVPXSVQVRDVSVTVRWAAWIDWBWC
    UQ $.

  $( Working in base ` B ` , if the fraction
     ` ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) ) ` is equal to the result of
     incorrectly cancelling the common digit ` W ` iff that common digit has a
     value determined only by ` B ` , ` T ` , and ` U ` .  The condition
     ` U =/= ( B x. T ) ` is eliminated.

     (Contributed by Richard Penner, 24-Oct-2019.) $)
  rp-anomcanlem1 $p |- ( ( ( B e. CC /\ W e. CC ) /\ ( T e. CC /\ U e. CC )
                           /\ ( U =/= 0 /\ U =/= ( B x. T )
                                /\ ( ( B x. W ) + U ) =/= 0 ) )
                         -> ( ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) )
                              = ( T / U )
                            <-> W = ( ( ( B - 1 ) x. ( T x. U ) )
                                      / ( ( B x. T ) - U ) ) ) ) $=
    ( cc wcel wa cc0 wne cmul co caddc w3a cdiv wceq cmin mulcld addcld 3bitrd
    c1 simp1l simp2l simp1r simp2r simp33 simp31 adddird adddid eqeq12d addcomd
    divmuleqd eqeq1d mul12d mulcomd oveq2d 3eqtrd oveq1d mulassd mulid2d eqcomd
    addsubeq4d oveq12d 1cnd subdird eqtr4d eqcom a1i subdid subcld simp32 simp1
    wb simp2 simp3 necomd subne0d syl3anc divmul3d 3bitr4d ) AEFZDEFZGZBEFZCEFZ
    GZCHIZCABJKZIZADJKZCLKZHIZMZMZWGDLKZWJNKBCNKOWNCJKZBWJJKZOWGCJKZDCJKZLKZBWI
    JKZBCJKZLKZOZDATPKZXAJKZWGCPKZNKZOZWMWNWJBCWMWGDWMABVTWAWEWLUAZWBWCWDWLUBZQ
    ZVTWAWEWLUCZRWMWICWMADXIXLQZWBWCWDWLUDZRXJXNWBWEWFWHWKUEWBWEWFWHWKUFUKWMWOW
    SWPXBWMWGDCXKXLXNUGWMBWICXJXMXNUHUIWMXCWRWQLKZXBOWTWRPKZWQXAPKZOZXHWMWSXOXB
    WMWQWRWMWGCXKXNQZWMDCXLXNQZUJULWMWRWQWTXAXTXSWMBWIXJXMQWMBCXJXNQZVAWMXRDWGJ
    KZWRPKZXEOZXGDOZXHWMXPYCXQXEWMWTYBWRPWMWTABDJKZJKADBJKZJKYBWMBADXJXIXLUMWMY
    FYGAJWMBDXJXLUNUOWMADBXIXLXJUMUPUQWMXQAXAJKZTXAJKZPKXEWMWQYHXAYIPWMABCXIXJX
    NURWMYIXAWMXAYAUSUTVBWMATXAXIWMVCZYAVDVEUIWMDXFJKZXEOZXEYKOZYDYEYLYMVLWMYKX
    EVFVGWMYCYKXEWMYKYCWMDWGCXLXKXNVHUTULWMXEDXFWMXDXAWMATXIYJVIYAQXLWMWGCXKXNV
    IWMWGEFZWDWHXFHIXKXNWBWEWFWHWKVJYNWDWHMZWGCYNWDWHVKYNWDWHVMYOCWGYNWDWHVNVOV
    PVQVRVSYEXHVLWMXGDVFVGSSS $.

  $( Working in base ` B ` , if the fraction
     ` ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) ) ` is equal to the result of
     incorrectly cancelling the common digit ` W ` , the additional condition,
     ` U = ( B x. T ) ` , results in a sterile result.

     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-anomcanlem2 $p |- ( ( ( B e. CC /\ W e. CC ) /\ ( T e. CC /\ U e. CC )
                           /\ ( U =/= 0 /\ U = ( B x. T )
                                /\ ( ( B x. W ) + U ) =/= 0 ) )
                         -> ( ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) )
                              = ( T / U ) -> ( B = 1 /\ T = U ) ) ) $=
    ( cc wcel wa cc0 wne cmul co wceq caddc cdiv c1 eqcomd oveq2d addcld eqeq2d
    w3a simpl1 simpl2l simpl32 simpl31 simpl33 eqnetrd jca simpr 3eqtrd simpl1l
    eqnetrrd simpl2 mulcld simpl1r simpl3r simpl3l divmuleqd mpbid simp1l simp2
    simp1r adddid mulassd mulcomd oveq1d simp3l mulcan2d 3bitrd addcomd addcand
    eqeq1d bitrd mulid2d 1cnd mulne0bbd biimpd adantr mpd syl31anc simpll3 ax-1
    wi syl imp 3eqtr2rd mpdan ex ) AEFZDEFZGZBEFZCEFZGZCHIZCABJKZLZADJKZCMKZHIZ
    TZTZWODMKZWRNKZBCNKZLZAOLZBCLZGZXAXEGZXFXHXIWJWKWOHIZWQWOMKZHIZGZXBXKNKZBWO
    NKZLZXFWJWMWTXEUAWKWLWJWTXEUBXIXJXLXICWOHWNWPWSWJWMXEUCZWNWPWSWJWMXEUDUKXIX
    KWRHXIWOCWQMXICWOXQPQZWNWPWSWJWMXEUEUFUGXIXNXCXDXOXIXKWRXBNXRQXAXEUHXICWOBN
    XQQUIWJWKXMTZXPGZXBWOJKZBXKJKZLZXFXTXPYCXSXPUHXTXBXKBWOXTWODXTABWHWIWKXMXPU
    JZWJWKXMXPULZUMZWHWIWKXMXPUNZRXTWQWOXTADYDYGUMYFRYEYFXJXLWJWKXPUOXJXLWJWKXP
    UPUQURXSYCXFWBXPXSYCXFXSYCXBDBMKZLZWOBLZXFXSYCYABAYHJKZJKZLYABAJKZYHJKZLZYI
    XSYBYLYAXSXKYKBJXSYKXKXSADBWHWIWKXMUSZWHWIWKXMVAZWJWKXMUTZVBPQSXSYLYNYAXSYN
    YLXSBAYHYRYPXSDBYQYRRZVCPSXSYOYAWOYHJKZLYAYHWOJKZLYIXSYNYTYAXSYMWOYHJXSBAYR
    YPVDVESXSYTUUAYAXSWOYHXSABYPYRUMZYSVDSXSXBYHWOXSWODUUBYQRYSUUBWJWKXJXLVFZVG
    VHVHXSYIDWOMKZYHLYJXSXBUUDYHXSWODUUBYQVIVKXSDWOBYQUUBYRVJVLXSYJWOOBJKZLXFXS
    BUUEWOXSUUEBXSBYRVMPSXSAOBYPXSVNYRXSABYPYRUUCVOVGVLVHVPVQVRVSXIXFGZXFXGXIXF
    UHZUUFCWOUUEBUUFWTWPWJWMWTXEXFVTWNWPWSUTWCUUFOABJUUFAOUUGPVEUUFBXIXFWKXIWMX
    FWKWBZWJWMWTXEULWKUUHWLWKXFWAVQWCWDVMWEUGWFWG $.

  ${

    rp-propercan.a $e |- ( ph -> A e. CC ) $.
    rp-propercan.b $e |- ( ph -> B e. CC ) $.
    rp-propercan.bne0 $e |- ( ph -> B =/= 0 ) $.
    rp-propercan.c $e |- ( ph -> C e. CC ) $.
    rp-propercan.cne0 $e |- ( ph -> C =/= 0 ) $.
    $( Proper cancellation when common factor multiplies from the front.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan3ALT $p |- ( ph -> ( ( B x. A ) / ( B x. C ) ) = ( A / C ) ) $=
      ( divcan5d ) ABDCEHFIGJ $.

    $( Proper cancellation when common factor is in the interior.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan1ALT $p |- ( ph -> ( ( A x. B ) / ( B x. C ) ) = ( A / C ) ) $=
      ( cmul co cdiv wceq rp-propercan3ALT mulcomd oveq1d eqeq1d mpbid ) ACBJKZ
      CDJKZLKZBDLKZMBCJKZTLKZUBMABCDEFGHINAUAUDUBASUCTLACBFEOPQR $.

    $( Proper cancellation when common factor is last.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan2ALT $p |- ( ph -> ( ( A x. B ) / ( C x. B ) ) = ( A / C ) ) $=
      ( divcan5rd ) ABDCEHFIGJ $.

    $( Proper cancellation when common factor is on exterior.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan4ALT $p |- ( ph -> ( ( B x. A ) / ( C x. B ) ) = ( A / C ) ) $=
      ( cmul co cdiv wceq rp-propercan2ALT mulcomd oveq1d eqeq1d mpbid ) ABCJKZ
      DCJKZLKZBDLKZMCBJKZTLKZUBMABCDEFGHINAUAUDUBASUCTLABCEFOPQR $.
  $}

  ${
    rp-propercan.acn $e |- ( ph -> A e. CC ) $.
    rp-propercan.ccn $e |- ( ph -> C e. CC ) $.
    rp-propercan.cne $e |- ( ph -> C =/= 0 ) $.
    $( Proper cancellation when common factor is 10 and we use the decimal
       operator to represent two-digit terms.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan5ALT $p |- ( ph -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
      ( c10 cmul cdiv wceq cc0 cdc 10nn a1i caddc df-dec mulcld addid1d eqtr2d
      co cc wcel nncni wne nnne0i rp-propercan3ALT oveq12d eqeq1d mpbid ) AGBHT
      ZGCHTZITZBCITZJBKLZCKLZITZUMJABGCDGUAUBAGMUCNZGKUDAGMUENEFUFAULUPUMAUJUNU
      KUOIAUNUJKOTZUJUNURJABKPNAUJAGBUQDQRSAUOUKKOTZUKUOUSJACKPNAUKAGCUQEQRSUGU
      HUI $.
  $}

  ${
    rp-propercan.ann0 $e |- ( ph -> A e. NN0 ) $.
    rp-propercan.cnn $e |- ( ph -> C e. NN ) $.
    $( Proper cancellation when common factor is 10 and we use the decimal
       operator to represent two-digit terms.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan6ALT $p |- ( ph -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
      ( cn0 wcel cc nn0cn syl cn nncn cc0 wne nnne0 rp-propercan5ALT ) ABCABFGB
      HGDBIJACKGZCHGECLJAQCMNECOJP $.
  $}

  $( "We all know that 9/12 is equivalent to 3/4". -Thomas P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-propercanex1ALT $p |- ( 9 / ; 1 2 ) = ( 3 / 4 ) $=
    ( c9 c1 c2 cdiv co c3 cmul c4 3t3e9 eqcomi 4t3e12 oveq12i wtru wceq cc wcel
    cdc a1i cc0 wne tru 3cn 3ne0 4cn 4ne0 rp-propercan4ALT ax-mp eqtri ) ABCQZD
    EFFGEZHFGEZDEZFHDEZAUJUIUKDUJAIJUKUIKJLMULUMNUAMFFHFOPMUBRZUNFSTMUCRHOPMUDR
    HSTMUERUFUGUH $.

  $( "We all know ... that 21/56 is equivalent to 3/8." -Thomas P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-propercanex2ALT $p |- ( ; 2 1 / ; 5 6 ) = ( 3 / 8 ) $=
  ( c2 c1 cdc c5 c6 cdiv co c7 c3 cmul c8 7t3e21 eqcomi wtru cc wcel a1i nnne0i
  cc0 wne 8t7e56 oveq12i wceq tru 3cn 7cn 7nn 8cn rp-propercan4ALT ax-mp eqtri
  8nn ) ABCZDECZFGHIJGZKHJGZFGZIKFGZUMUOUNUPFUOUMLMUPUNUAMUBNUQURUCUDNIHKIOPNUE
  QHOPNUFQHSTNHUGRQKOPNUHQKSTNKULRQUIUJUK $.

  $( "It is somewhat interesting to note that 16/64 is equal to 1/4". -Thomas
     P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-propercanex3ALT $p |- ( ; 1 6 / ; 6 4 ) = ( 1 / 4 ) $=
    ( c1 c6 c4 cdiv co cmul c8 cc 8p8e16 8cn eqcomi eqtri wtru wcel a1i cc0 8re
    c2 cr ax-mp cdc caddc addcli eqeltrri mulid2i 2timesi 4cn 2cn mulassi 4t2e8
    oveq2i oveq1i 3eqtri 8t8e64 oveq12i wceq tru ax-1cn wne readdcli eleq1a clt
    wi 8pos addgt0ii breqtri gt0ne0ii 4ne0 rp-propercan2ALT ) ABUAZBCUAZDEAVJFE
    ZCVJFEZDEZACDEZVJVLVKVMDVLVJVJGGUBEZVJHIGGJJUCUDZUEKVMVKVMGGFEZVKVMCRGFEZFE
    ZCRFEZGFEZVRVJVSCFVSVJVSVPVJGJUFILKUKWBVTCRGUGUHJUIKWAGGFUJULUMUNLKUOMVNVOU
    PUQMAVJCAHNMUROVJHNMVQOVJPUSMVJVJVPUPZVJSNZVPVJIKVPSNWCWDVCGGQQUTVPSVJVATTP
    VPVJVBGGQQVDVDVEIVFVGOCHNMUGOCPUSMVHOVITL $.

  $( "The fraction 19/95 is equal to 1/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 39. $)
  rp-propercanex4ALT $p |- ( ; 1 9 / ; 9 5 ) = ( 1 / 5 ) $=
    (  ) ? $.

  $( "Also 26/65 equals to 2/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 40. $)
  rp-propercanex5ALT $p |- ( ; 2 6 / ; 6 5 ) = ( 2 / 5 ) $=
    (  ) ? $.

  $( "484/847 = 4/7". -Thomas P. Dence.

     Statement of [Dence1983] p. 40. $)
  rp-propercanex6ALT $p |- ( ; ; 4 8 4 / ; ; 8 4 7 ) = ( 4 / 7 ) $=
    (  ) ? $.

  ${
    rp-anomcanlem.b $e |- ( ph -> B e. CC ) $.
    rp-anomcanlem.w $e |- ( ph -> W e. CC ) $.
    rp-anomcanlem.t $e |- ( ph -> T e. CC ) $.
    rp-anomcanlem.u $e |- ( ph -> U e. CC ) $.
    rp-anomcanlem.une0 $e |- ( ph -> U =/= 0 ) $.
    rp-anomcanlem.demne0 $e |- ( ph -> ( ( B x. W ) + U ) =/= 0 ) $.
    ${
      rp-anomcanlem.canw $e |- ( ph -> U =/= ( B x. T ) ) $.
      $( Working in base ` B ` , if the fraction
         ` ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) ) ` is equal to the result
         of incorrectly cancelling the common digit ` W ` iff that common digit
         has a value determined only by ` B ` , ` T ` , and ` U ` .  The
         condition ` U =/= ( B x. T ) ` is eliminated. $)
      rp-anomcanlem1ALT $p |- ( ph
                         -> ( ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) )
                              = ( T / U )
                            <-> W = ( ( ( B - 1 ) x. ( T x. U ) )
                                      / ( ( B x. T ) - U ) ) ) ) $=
        (  ) ? $.
    $}

    ${
      rp-anomcanlem.cantw $e |- ( ph -> U = ( B x. T ) ) $.
      $( Working in base ` B ` , if the fraction
         ` ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) ) ` is equal to the result
         of incorrectly cancelling the common digit ` W ` , the additional
         condition, ` U = ( B x. T ) ` , results in a sterile result. $)
      rp-anomcanlem2ALT $p |- ( ph
                         -> ( ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) )
                              = ( T / U ) -> ( B = 1 /\ T = U ) ) ) $=
        (  ) ? $.
    $}
  $}
