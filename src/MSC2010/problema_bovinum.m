(*
Name: problema bovinum
Name: problema Archimedis
Name: Archimedes's cattle problem

URL: https://www.math.nyu.edu/~crorres/Archimedes/Cattle/Statement_text.html
URL: http://mathworld.wolfram.com/ArchimedesCattleProblem.html
URL: https://archive.lib.msu.edu/crcmath/math/math/a/a307.htm
URL: https://www.math.nyu.edu/~crorres/Archimedes/Cattle/cattle_vardi.pdf
URL: https://www.andrews.edu/~calkins/profess/cattle.htm
URL: http://www2.washjeff.edu/users/mwoltermann/Dorrie/1.pdf
URL: https://en.wikipedia.org/wiki/Archimedes%27s_cattle_problem
URL: http://digitale.bibliothek.uni-halle.de/vd18/content/pageview/4023090
URL: http://www.ams.org/notices/200202/fea-lenstra.pdf
URL: https://www.jstor.org/stable/2968125
URL: https://www.jstor.org/stable/2003954
URL: https://www.jstor.org/stable/2589706
URL: http://muse.jhu.edu/article/546726
URL: https://oeis.org/A096151
URL: http://www.math.vt.edu/people/brown/doc/cfrax.pdf
URL: http://web.archive.org/web/20071019001307/http://veling.nl/anne/templars/Solution.html
URL: https://www.math.nyu.edu/~crorres/Archimedes/Cattle/Solution2.html


	
PellSolve[(m_Integer)?Positive] := Module[ {cf, n, s},
cf = ContinuedFraction[ Sqrt[m]];
n = Length[ Last[cf]];
If[ OddQ[n], n = 2*n];
s = FromContinuedFraction[ ContinuedFraction[ Sqrt[m], n]];
{Numerator[s], Denominator[s]}
];

x = 4729494;
y = PellSolve[x];
z = Floor[25194541/184119152(y[[1]] + y[[2]]*Sqrt[x])^4658];
Take[ IntegerDigits[z], 105] 



-----

dPrime = 609 * 7766 ;
d = dPrime * (2 * 4657)^2  ;
{root609, root7766, rootDPrime, w} = ToNumberField[{
    Sqrt[609], Sqrt[7766], Sqrt[dPrime],
    300426607914281713365 Sqrt[609] + 84129507677858393258 Sqrt[7766]
}, All] ;
k[j_] := (w^( 4658 j) - w^(-4658 j ))^2 / ( 4657 * 79072 ) ;
T = 50389082 k[1]


*)

(* Statement of the Problem *)

(* Part One *)

(*

Πρόβλημα,
ὃπερ Ἀρχιμήδης ἐν ἐπιγράμμασιν εὑρὼν τοῖς ἐν Ἀλεξανδρείᾳ περὶ ταῦτα πραγματευομένοις ζητεῖν ἀπέστειλεν ἐν τῇ πρὸς Ἐρατοσθένην τὸν Κυρηναῖον ἐπιστολῇ.

Πληθὺν Ἠελίοιο βοῶν, ὦ ξεῖνε, μέτρησον 
    φροντίδ᾽ ἐπιστήσας, εἰ μετέχεις σοφίης, 
πόσση ἄρ᾽ ἐν πεδίοις Σικελῆς ποτ᾽ ἐβόσκετο νήσου 
    Θρινακίης τετραχῇ στίφεα δασσαμένη 
χροίην ἀλλάσσοντα˙ τὸ μὲν λευκοῖο γάλακτος, 
    κυανέῳ δ᾽ ἕτερον χρώματι λαμπόμενον, 
ἂλλο γε μὲν ξανθόν, τὸ δὲ ποικίλον. ἐν δὲ ἑκάστῳ 
    στίφει ἔσαν ταῦροι πλήθεσι βριθόμενοι 
συμμετρίης τοιῆσδε τετευχότες˙ ἀργότριχας μὲν 
    κυανέων ταύρων ἡμίσει ἠδὲ τρίτῳ 
καὶ ξανθοῖς σύμπασιν ἴσους, ὦ ξεῖνε, νόησον, 
    αὐτὰρ κυανέους τῷ τετράτῳ τε μέρει 
μικτοχρόων καὶ πέμπτῳ, ἔτι ξανθοῖσί τε πᾶσιν. 
    τοὺς δ᾽ ὑπολειπομένους ποικιλόχρωτας ἄθρει 
ἀργεννῶν ταύρων ἓκτῳ μέρει ἑβδομάτῳ τε 
    καὶ ξανθοῖς αὖτις πᾶσιν ἰσαζομένους. 
θηλείαισι δὲ βουσὶ τάδ᾽ ἒπλετο˙ λευκότριχες μέν 
    ἦσαν συμπάσης κυανέης ἀγέλης 
τῷ τριτάτῳ τε μέρει καὶ τετράτῳ ἀτρεκὲς ἶσαι˙ 
    αὐτὰρ κυάνεαι τῷ τετράτῳ τε πάλιν 
μικτοχρόων καὶ πέμπτῳ ὁμοῦ μέρει ἰσάζοντο 
    σὺν ταύροις˙ πάσης δ᾽ εἰς νομὸν ἐρχομένης 
ξανθοτρίχων ἀγέλης πέμπτῳ μέρει ἠδὲ καὶ ἓκτῳ 
    ποικίλαι ἰσάριθμον πλῆθος ἒχον τετραχῇ. 
ξανθαὶ δ᾽ ἠριθμεῦντο μέρους τρίτου ἡμίσει ἶσαι 
    ἀργεννῆς ἀγέλη ἑβδομάτῳ τε μέρει. 
ξεῖνε, σὺ δ᾽ Ἠελίοιο βοῶν πόσαι ἀτρεκὲς εἰπών, 
    χωρὶς μὲν ταύρων ζατρεφέων ἀριθμόν, 
χωρὶς δ᾽ αὖ θήλειαι ὅσαι κατὰ χρῶμα ἓκασται, 
    οὐκ ἄιδρίς κε λέγοι᾽ οὐδ᾽ ἀριθμῶν ἀδαής, 
οὐ μήν πώ γε σοφοῖς ἐναρίθμιος. ἀλλ᾽ ἴθι φράζευ 
    καὶ τάδε πάντα βοῶν Ἠελίοιο πάθη. 
ἀργότριχες ταῦροι μὲν ἐπεὶ μιξαίατο πληθὺν 
    κυανέοις, ἵσταντ᾽ ἔμπεδον ἰσόμετροι 
εἰς βάθος εἰς εὖρός τε, τὰ δ᾽ αὖ περιμήκεα πάντῃ 
    πίμπλαντο πλίνθου Θρινακίης πεδία. 
ξανθοὶ δ᾽ αὖτ᾽ εἰς ἓν καὶ ποικίλοι ἀθροισθέντες 
    ἵσταντ᾽ ἀμβολάδην ἐξ ἑνος ἀρχόμενοι 
σχῆμα τελειοῦντες τὸ τρικράσπεδον οὔτε προσόντων 
    ἀλλοχρόων ταύρων οὔτ᾽ ἐπιλειπομένων. 
ταύτα συνεξευρὼν καὶ ἐνὶ πραπίδεσσιν ἀθροίσας 
    καὶ πληθέων ἀποδοὺς, ὦ ξένε, πὰντα μέτρα 
ἔρχεο κυδιόων νικηφόρος, ἴσθι τε πάντως 
    κεκριμένος ταύτῃ ὄμπνιος ἐν σοφἰῃ.


*)

bovineRelation[count1_, fraction1_, fraction2_, count2_, count3_ ] := Module[
{ k = Denominator[ fraction1 + fraction2 ] }, 
Expand[k ( -  count1 +  (fraction1 + fraction2) count2 + count3 ) ] 
];
poly1 = bovineRelation[countWhiteBulls, 1/2, 1/3, countBlackBulls, countYellowBulls] ;
poly2 = bovineRelation[countBlackBulls, 1/4, 1/5, countDappledBulls, countYellowBulls] ;
poly3 = bovineRelation[countDappledBulls, 1/6, 1/7, countWhiteBulls, countYellowBulls] ;
poly4 = bovineRelation[countWhiteCows, 1/3, 1/4, countBlackBulls + countBlackCows, 0] ;
poly5 = bovineRelation[countBlackCows, 1/4, 1/5, countDappledBulls + countDappledCows, 0] ;
poly6 = bovineRelation[countDappledCows, 1/5, 1/6, countYellowBulls + countYellowCows, 0]  ;
poly7 = bovineRelation[countYellowCows, 1/6, 1/7, countWhiteBulls + countWhiteCows, 0 ] ;
polyList = {poly1, poly2, poly3, poly4, poly5, poly6, poly7} ;
variableList = { 
countWhiteBulls, countBlackBulls, countYellowBulls, countDappledBulls, 
countWhiteCows, countBlackCows, countYellowCows, countDappledCows
};
polyToMatrixRow[poly_] := Map[Coefficient[poly, # ] &, variableList] ;
bovineMatrix = Map[polyToMatrixRow, polyList];
rawPartOneSolution = NullSpace[bovineMatrix][[1]];
forceIntegerSolutionFactor = Apply[LCM, Map[Denominator,rawPartOneSolution]];
partOneSolution = MapThread[Rule, {variableList, rawPartOneSolution * forceIntegerSolutionFactor * arbitraryInteger}];

(* Test:  AllTrue[Map[ # == 0 &, polyList /. partOneSolution]] *)

squareNumber = countWhiteBulls + countBlackBulls ;
triangleNumber = countYellowBulls + countDappledBulls ;
Apply[ GCD, ({ squareNumber, triangleNumber  } /. partOneSolution /. { arbitraryInteger -> 1 } )]

