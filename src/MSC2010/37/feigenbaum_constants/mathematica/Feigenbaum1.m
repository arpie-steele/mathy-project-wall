(* Logistic Map, optimized for calculation when r or x are computationally expensive *)
forward[r_, x_] := r ( 1/4 - ( x - 1/2)^2 ) ;
(* Interval-arithmatic-optimized logistic inverse relation *)
reverse[r_, y_ ] := Module[{halfgap = Sqrt[IntervalIntersection[Interval[{0,1/4}], 1/4 - y/r]]}, IntervalIntersection[Interval[{-1/2,1/2}], IntervalUnion[-halfgap, halfgap]] + 1/2];
(* Calculate difference between iterated logistic map and the y=x relation *)
delta[r_, x_, n_ ] := delta[r, x, n] = Factor[Expand[Nest[forward[r, #] &, x, n]]-x];
(* Calculate fixed n-cycles and fixed points, 1-cycles *)
points1 = Solve[delta[r0, x0, 1] == 0, {x0}];
points2 = Solve[delta[r0, x0, 2] == 0, {x0}];
points3 = Solve[delta[r0, x0, 3] == 0, {x0}];
points4 = Solve[delta[r0, x0, 4] == 0, {x0}];

(* When r < 1, x = 0 is a stable fixed point *)
Reduce[ ( D[delta[r0, x0, 1], x0] /. points1[[1]] )< 0, {r0}]
(* When r > 1, x = 1 - 1/r is a stable fixed point *)
Reduce[ ( D[delta[r0, x0, 1], x0] /. points1[[2]] )< 0, {r0}]
(* r = 1 is also the point where the stable fixed point jumps from solution 1 to solution 2 *)
Solve[ ( x0 /. points1[[1]] ) == ( x0 /. points1[[2]] ), r0, Reals]

(* Stable 2-cycles  begin  at 3 *)
Solve[ 1 < r0 < 4 && ( x0 /. points2[[3]] ) == ( x0 /. points2[[4]] ), r0, Reals]
(* When r > 3, ( 1 + r ± √((r-3)(r+1)) )/(2 r) are stable fixed points *)
Reduce[ ( D[delta[r0, x0, 2], x0] /. points2[[3]] )< 0, {r0}]
Reduce[ ( D[delta[r0, x0, 2], x0] /. points2[[4]] )< 0, {r0}]

(* Stable 3-cycles  begin  at 1 + Sqrt[8] *)
Solve[ 1 < r0 < 4 && ( x0 /. points3[[3]] ) == ( x0 /. points3[[4]] ), r0, Reals]
Plot[( x0 /. points3[[{3, 4, 5, 6, 7, 8}]]) , {r0, 1 + Sqrt[8], 4}]
Reduce[ ( D[delta[r0, x0, 3], x0] /. points3[[3]] )< 0 && 1 + Sqrt[8] < r0 < 4, {r0}]
Reduce[ ( D[delta[r0, x0, 3], x0] /. points3[[5]] )< 0 && 1 + Sqrt[8] < r0 < 4, {r0}]
Reduce[ ( D[delta[r0, x0, 3], x0] /. points3[[8]] )< 0 && 1 + Sqrt[8] < r0 < 4, {r0}]


(* We only have confidence in this technique up to a point, since the number of real solutions can change *)
Solve[ 3 < r0 < 7/2&& ( x0 /. points4[[5]] ) == ( x0 /. points4[[6]] ), r0, Reals]
Solve[ 1 + Sqrt[8] < r0 < 4 && ( x0 /. points4[[10]] ) == ( x0 /. points4[[11]] ), r0, Reals]
Reduce[ ( D[delta[r0, x0, 4], x0] /. points4[[5]] )< 0 && 1 + Sqrt[6] < r0 < 1 + Sqrt[4 + CubeRoot[108]], {r0}]


(* Plot the fixed points found by analysis *)
Show[ Plot[( x0 /. points1[[1]]) , {r0, 0 , 1}],
Plot[( x0 /. points1[[2]]) , {r0, 1 , 4}],
Plot[x0 /. points2[[{3, 4}]], {r0, 3, 4}],
Plot[( x0 /. points3[[{3, 5, 8}]]) , {r0, 1 + Sqrt[8], 4}],
Plot[( x0 /. points4[[{5, 6, 7, 8}]]) , {r0,1+ Sqrt[6], 1 + Sqrt[4 + CubeRoot[108]]}],
Plot[( x0 /. points4[[{5, 6, 7, 8, 9, 10, 11, 12}]]) , {r0, N[1 + Sqrt[4 + CubeRoot[108]]], 4}],
PlotRange->{{0, 4}, {0, 1}}, AxesOrigin->{0,0}]



(* https://arxiv.org/pdf/1008.4608.pdf *)
z = 2;
d = z/2;
n = 5;
xs = Table[Cos[j Pi/n], {j, 1, n}];
g[x_, t_] := Sum[ ( 1 - Boole[k==1]/2 ) t[[k]] ChebyshevT[2k - 2, x^d], {k, 1, Length[t]}];
g0[t_] := Sum[ ( 1 - Boole[k==1]/2 ) t[[k]] (-1)^(k+1), {k, 1, Length[t]}];
g1[t_] := Sum[ ( 1 - Boole[k==1]/2 ) t[[k]], {k, 1, Length[t]}];
dxg[x_, t_] := Sum[ t[[k]] (2k - 2 ) ChebyshevU[2k - 3, x^d] x^(d-1), {k, 2, Length[t]}];

dtkfa[x_, t_, k_] := ( 1 - Boole[k==1]/2 ) ChebyshevT[2k - 2, g[ -g1[t] x, t]^d + If[d == 1, 1, d g[ -g1[t] x, t]^(d-1) ]  ( 1 - Boole[k==1]/2 ) ChebyshevT[2k - 2, (-g1[t] x)^d] Sum[ t[[l]] (2l - 2 ) ChebyshevU[2l - 3, g[ -g1[t] x, t]^d ], {l, 2, Length[t]}];

dtkfb[x_, t_, k_] := ( 1 - Boole[k==1]/2 ) ( - g[x, 




Clear[n, x, y, fx, fy, fz, cx, cy, cz] ;
n= 5;
cy[k_ ] := ( cy[k] = Sum[ Boole[EvenQ[k+j]]Binomial[k+j,j] cx[k+j] cy[0]^j, {j, 0, 2n-k}] )  /; k > 0
fy = SeriesData[x, cy[0], Table[cy[k],{k,0,2n}], 0, 1+2n, 1] ;
fx =  1 + SeriesData[x, 0, Table[Boole[EvenQ[k]]cx[k], {k, 2, 2n+1}], 2, 2n+2, 1] ;
CoefficientList[Expand[Normal[fy] - Normal[fx]], x, 1 + 2 n]


ClearAll[m, initialC, g, fc, t]
(* eqn 2.1 of arxiv.org/1602.02357 *)
g[c_, x_ ] := Sum[ c[[j]] ChebyshevT[2j -2, x], {j, 1, Length[c]} ] - c[[1]] / 2 ;
(* eqn 2.2 of arxiv.org/1602.02357 *)
fc[c_, x_ ] := g[c, 1] g[c, x] - g[c, g[c, g[c, 1] x ] ] ;
(* eqn 2.3 of arxiv.org/1602.02357 *)
t[n_, i_ ] := Cos[( 2 i - 1) Pi / (4 n ) ] /; n >= 2 && 1 <= i <= n ;
(* eqn 2.5 of arxiv.org/1602.02357 *)
m[n_] := ( m[n] = Floor[(3/2) Sqrt[n]] ) /; n >= 2;
initialC[2] = { 6/10,  -7/10 };

