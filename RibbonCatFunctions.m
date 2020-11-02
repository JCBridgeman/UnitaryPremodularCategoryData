(* ::Package:: *)

polarForm=Expand[#/.z_?NumericQ:>Abs[z] Exp[I Arg[z]]]&;


fusionproduct[a_,b_]/;MemberQ[obs,a]&&MemberQ[obs,b]:=fusionproduct[a,b]=DeleteCases[Table[If[V[a,b][c]=!=0,c],{c,obs}],Null]

dim[a_]/;MemberQ[obs,a]:=dim[a]=Module[{d0,dimeqs,dimsol,da},
dimeqs=Join[
Outer[d0[#1]d0[#2]==Sum[V[#1,#2][x]d0[x],{x,fusionproduct[#1,#2]}]&,obs,obs]//Flatten
,d0[#]>=1&/@obs];
da:=d0[a]//.Solve[dimeqs][[1]]//RootReduce//FullSimplify//ToRadicals;
Return[da]];

dtot[]:=dtot[]=Sqrt[Total[dim[#]^2&/@obs]]//RootReduce//FullSimplify//ToRadicals
dtot[X_]:=dtot[X]=Sqrt[Total[dim[#]^2&/@X]]//RootReduce//FullSimplify//ToRadicals

dual[a_]/;MemberQ[obs,a]:=dual[a]=Module[{v=Abs[V[a,#][unit]]&/@obs},obs[[Position[v,1][[1,1]]]]]
OverBar[a_]/;MemberQ[obs,a]:=dual[a]

dim[{A__}]:=Sum[dim[a],{a,{A}}]


F[a_,b_,c_][d_][e_,f_]:=0

F[a_,b_,u_][c_][c_,b_]/;(u===unit&&MemberQ[fusionproduct[a,b],c]):=1;
F[a_,u_,b_][c_][a_,b_]/;(u===unit&&MemberQ[fusionproduct[a,b],c]):=1;
F[u_,a_,b_][c_][a_,c_]/;(u===unit&&MemberQ[fusionproduct[a,b],c]):=1;

F[a_,b_,c_][d_][e_,f_]/;MemberQ[fusionproduct[a,b],e]&&MemberQ[fusionproduct[b,c],f]&&MemberQ[Intersection[fusionproduct[e,c],fusionproduct[a,f]],d]:=F[a,b,c][d][e,f]=
X0[a,b,c][d][e,f]//.rep0//RootReduce//FullSimplify


pentagons[a_,b_,c_,d_]:=pentagons[a,b,c,d]=Table[
F[f,c,d][e][g,x]F[a,b,x][e][f,y]==
Sum[F[a,b,c][g][f,z]F[a,z,d][e][g,y]F[b,c,d][y][z,x],{z,fusionproduct[b,c]}]
,{f,fusionproduct[a,b]},{g,fusionproduct[f,c]},{x,fusionproduct[c,d]},{y,fusionproduct[b,x]},{e,Intersection[fusionproduct[g,d],fusionproduct[a,y]]}
]//Flatten//DeleteCases[True]

allpentagons:=allpentagons=Table[pentagons[a,b,c,d],{a,obs},{b,obs},{c,obs},{d,obs}]//Flatten//DeleteCases[True]//DeleteDuplicates

nicepentagons:=nicepentagons=Module[
{a,b,c,d,pents={}},
Do[If[Length[fusionproduct[b,c]]==1,
AppendTo[pents,Table[pentagons[a,b,c,d],{a,obs},{d,obs}]//Flatten]
],{b,obs},{c,obs}];
Return[pents//Flatten//DeleteDuplicates];
]

unitaryFL:=unitaryFL=Table[
Sum[F[a,b,c][d][e,f]Conjugate[F[a,b,c][d][g,f]],{f,fusionproduct[b,c]}]==If[e===g,1,0]
,{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{g,fusionproduct[a,b]},{d,fusionproduct[e,c]}]//Flatten//DeleteCases[True]//DeleteDuplicates

unitaryFR:=unitaryFR=Table[
Sum[F[a,b,c][d][f,e]Conjugate[F[a,b,c][d][f,g]],{f,fusionproduct[a,b]}]==If[e===g,1,0]
,{a,obs},{b,obs},{c,obs},{e,fusionproduct[b,c]},{g,fusionproduct[b,c]},{d,fusionproduct[a,e]}]//Flatten//DeleteCases[True]//DeleteDuplicates

unitaryF:=unitaryF=Join[unitaryFL,unitaryFR]//DeleteDuplicates;

simpleunitary:=DeleteCases[Table[
If[Length[fusionproduct[a,b]]==1||Length[fusionproduct[b,c]]==1,X0[a,b,c][d][e,f]->\[Phi][a,b,c][d][e,f]],{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten,Null]//DeleteDuplicates;

Fs:=Fs=Table[F[a,b,c][d][e,f],{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten

newF[a_,b_,c_][d_][e_,f_]/;MemberQ[fusionproduct[a,b],e]&&MemberQ[fusionproduct[b,c],f]&&MemberQ[Intersection[fusionproduct[e,c],fusionproduct[a,f]],d]:=newF[a,b,c][d][e,f]=
F[a,b,c][d][e,f]U[b,c][f]U[a,f][d]Conjugate[U[a,b][e]U[e,c][d]]

\[Kappa][x_]:=F[x,dual[x],x][x][unit,unit]dim[x]//FullSimplify

new\[Kappa][x_]:=newF[x,dual[x],x][x][unit,unit]dim[x]//FullSimplify

cleanupFs[ns_]:=Module[{relabF0,relabR0,P,T,M=$Assumptions,Q},
relabF0=Table[X0[a,b,c][d][e,f]->FullSimplify[F[a,b,c][d][e,f]//.ns],{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[e,c],fusionproduct[a,f]]}]//Flatten;
P=DeleteCases[relabF0,_?(#[[1]]===#[[2]]&)];
Q=Join[P];
Return[Q];
]

reguageF[ns_]:=Module[{relabF0,relabR0,P,T,M=$Assumptions,Q},
relabF0=Table[X0[a,b,c][d][e,f]->Simplify[newF[a,b,c][d][e,f]//.ns//RootReduce]//Refine,{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[e,c],fusionproduct[a,f]]}]//Flatten;
P=DeleteCases[relabF0,_?(#[[1]]===#[[2]]&)];

Q=Join[P];
Return[Q];
]


A[a_,b_][c_]:=Conjugate[F[dual[a],a,b][b][unit,c]]Sqrt[(dim[a]dim[b])/dim[c]]
A[c_][a_,b_]:=F[dual[a],a,b][b][unit,c]Sqrt[(dim[a]dim[b])/dim[c]]

B[a_,b_][c_]:=F[a,b,dual[b]][a][c,unit]Sqrt[(dim[a]dim[b])/dim[c]]
B[c_][a_,b_]:=Conjugate[F[a,b,dual[b]][a][c,unit]]Sqrt[(dim[a]dim[b])/dim[c]]

symmetry1:=symmetry1=
Table[
F[a,b,c][d][e,f]==1/Abs[\[Kappa][a]]^2 Sqrt[(dim[e]dim[f])/(dim[b]dim[d])]A[d][a,f]A[a,b][e]Conjugate[F[dual[a],e,c][f][b,d]],
{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten//RootReduce//DeleteCases[True]//DeleteDuplicates;

symmetry2:=symmetry2=
Table[
F[a,b,c][d][e,f]==1/Conjugate[\[Kappa][b]] Sqrt[(dim[e]dim[f])/(dim[a]dim[c])]A[f][b,c]B[a,b][e]Conjugate[F[e,dual[b],f][d][a,c]],
{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten//RootReduce//DeleteCases[True]//DeleteDuplicates;

symmetry3:=symmetry3=
Table[
F[a,b,c][d][e,f]==1/Abs[\[Kappa][c]]^2 Sqrt[(dim[e]dim[f])/(dim[b]dim[d])]B[f][b,c]B[e,c][d]Conjugate[F[a,f,dual[c]][e][d,b]],
{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten//RootReduce//DeleteCases[True]//DeleteDuplicates;

pivotalstar:=Table[
F[a,b,c][d][e,f]==1/(Conjugate[\[Kappa][a]]\[Kappa][c]) A[d][a,f]A[dual[a],e][b]B[f][b,c]B[d,dual[c]][e]F[dual[a],d,dual[c]][b][f,e],{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten//DeleteDuplicates//DeleteCases[True];


F[a_,b_][c_,d_][e_,f_]:=1/\[Kappa][d] B[e][c,d]F[a,b,dual[d]][c][e,f]B[b,dual[d]][f]


R[u_,a_][a_]/;(u===unit):=1
R[a_,u_][a_]/;(u===unit):=1

R[a_,b_][c_]/;MemberQ[Intersection[fusionproduct[a,b],fusionproduct[b,a]],c]:=R[a,b][c]=X0[a,b][c]//.rep0//RootReduce//FullSimplify

hexagon1[a_,b_,c_]:=hexagon1[a,b,c]=Table[
R[a,c][e]F[a,c,b][d][e,f]R[b,c][f]
==
Sum[F[c,a,b][d][e,g]R[g,c][d]F[a,b,c][d][g,f],{g,fusionproduct[a,b]}]
,{e,fusionproduct[a,c]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,b]]}]

hexagon2[a_,b_,c_]:=hexagon2[a,b,c]=Table[
Conjugate[R[c,a][e]]F[a,c,b][d][e,f]Conjugate[R[c,b][f]]
==
Sum[F[c,a,b][d][e,g]Conjugate[R[c,g][d]]F[a,b,c][d][g,f],{g,fusionproduct[a,b]}]
,{e,fusionproduct[a,c]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,b]]}
]

allhexagons:=allhexagons=Table[{hexagon1[a,b,c],hexagon2[a,b,c]},{a,obs},{b,obs},{c,obs}]//Flatten//DeleteDuplicates;

nicehexagons:=nicehexagons=Module[
{a,b,c,hex={}},
Do[If[Length[fusionproduct[a,b]]==1,
AppendTo[hex,Table[hexagon1[a,b,c],{c,obs}]//Flatten];
AppendTo[hex,Table[hexagon2[a,b,c],{c,obs}]//Flatten]
],{a,obs},{b,obs}];
Return[hex//Flatten//DeleteDuplicates];
]


unitaryR:=unitaryR=
Table[Abs[R[a,b][c]]==1
,{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten//DeleteCases[True]//DeleteDuplicates;

Rs:=Table[R[a,b][c],{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten
newR[a_,b_][c_]/;MemberQ[Intersection[fusionproduct[a,b],fusionproduct[b,a]],c]:=R[a,b][c]U[a,b][c]Conjugate[U[b,a][c]]

U[a_,u_][b_]/;(u===unit):=1;
U[u_,a_][b_]/;(u===unit):=1;


newFs:=newFs=Table[newF[a,b,c][d][e,f],{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[a,f],fusionproduct[e,c]]}]//Flatten
newRs:=Table[newR[a,b][c],{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten

unitaryU:=unitaryU=Table[
Abs[U[a,b][c]]==1
,{a,obs},{b,obs},{c,fusionproduct[a,b]}
]//Flatten//DeleteCases[True]//DeleteDuplicates

cleanupRs[ns_]:=Module[{relab,P,T,M=$Assumptions,Q},
relab=Table[X0[a,b][c]->FullSimplify[R[a,b][c]//.ns],{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten;
P=DeleteCases[relab,_?(#[[1]]===#[[2]]&)];
Return[P//ToRadicals];
]


reguageR[ns_]:=Module[{relabF0,relabR0,P,T,M=$Assumptions,Q},
relabR0=Table[X0[a,b][c]->Simplify[newR[a,b][c]//.ns//RootReduce]//Refine,{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten;

T=DeleteCases[relabR0,_?(#[[1]]===#[[2]]&)];

Q=Join[T];
Return[Q];
]


cleanup[ns_]:=Module[{relabF0,relabR0,P,T,M=$Assumptions,Q},
relabF0=Table[X0[a,b,c][d][e,f]->FullSimplify[F[a,b,c][d][e,f]//.ns//RootReduce],{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[e,c],fusionproduct[a,f]]}]//Flatten;
P=DeleteCases[relabF0,_?(#[[1]]===#[[2]]&)];

relabR0=Table[X0[a,b][c]->FullSimplify[R[a,b][c]//.ns//RootReduce],{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten;
Q=DeleteCases[relabR0,_?(#[[1]]===#[[2]]&)];

Q=Join[P,Q];
Return[Q];
]

reguage[ns_]:=Module[{relabF0,relabR0,P,T,M=$Assumptions,Q},
relabF0=Table[X0[a,b,c][d][e,f]->Simplify[newF[a,b,c][d][e,f]//.ns//RootReduce]//Refine,{a,obs},{b,obs},{c,obs},{e,fusionproduct[a,b]},{f,fusionproduct[b,c]},{d,Intersection[fusionproduct[e,c],fusionproduct[a,f]]}]//Flatten;
relabR0=Table[X0[a,b][c]->Simplify[newR[a,b][c]//.ns//RootReduce]//Refine,{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten;

P=DeleteCases[relabF0,_?(#[[1]]===#[[2]]&)];
T=DeleteCases[relabR0,_?(#[[1]]===#[[2]]&)];

Q=Join[P,T];
Return[Q];
]


\[Theta][x_]:=dim[x]Sum[F[x,x,dual[x]][x][e,unit]Conjugate[F[x,x,dual[x]][x][e,unit]]R[x,x][e],{e,fusionproduct[x,x]}]//RootReduce//FullSimplify

ribbonconditions:=ribbonconditions=Table[R[b,a][c]R[a,b][c]==\[Theta][c]/(\[Theta][a]\[Theta][b]),{a,obs},{b,obs},{c,fusionproduct[a,b]}]//Flatten//DeleteCases[True]//DeleteDuplicates

S:=S=1/dtot[] Table[Sum[\[Theta][x]/(\[Theta][a]\[Theta][dual[b]]) V[a,dual[b]][x]dim[x],{x,fusionproduct[a,dual[b]]}],{a,obs},{b,obs}]//RootReduce//Simplify

Z2[]:=Z2[]=Module[{FLAG=False,C={}},
Do[FLAG=False;

Do[
If[FullSimplify[\[Theta][x]/(\[Theta][a]\[Theta][b])]!=1,FLAG=True;Break[]]
,{b,obs},{x,fusionproduct[a,b]}];

If[FLAG==False,AppendTo[C,a]];
,{a,obs}];
Return[C]];


(*LinkedS[c_]:=1/dtot[]Table[Sum[Sqrt[dim[x]dim[a]dim[b]dim[c]]\[Theta][x]/(\[Theta][a]\[Theta][dual[b]])A[x][a,dual[b]][\[Mu],\[Nu]]F[dual[a],a,dual[b]][dual[b]][\[Sigma],c,\[Alpha]][\[Nu],x,\[Mu]]F[c,dual[b],b][c][\[Beta],dual[b],\[Sigma]][1,unit,1],{x,fusionproduct[a,dual[b]]},{\[Mu],V[a,dual[b]][x]}
,{\[Nu],V[dual[a],x][dual[b]]},{\[Sigma],V[c,dual[b]][dual[b]]}],{a,obs},{\[Alpha],V[dual[a],a][c]},{b,obs},{\[Beta],V[dual[b],b][c]}]*)
LinkedS[c_]:=1/dtot[] Table[Sum[Sqrt[dim[x]dim[a]dim[b]dim[c]] \[Theta][x]/(\[Theta][a]\[Theta][dual[b]]) A[x][a,dual[b]]Conjugate[F[dual[a],a,dual[b]][dual[b]][c,x]]F[c,dual[b],b][c][dual[b],unit],
{x,fusionproduct[a,dual[b]]}],{a,obs},{b,obs}]
SS[x_]:=ConjugateTranspose[LinkedS[x]].LinkedS[x]//RootReduce


TEE[]:=TEE[]=Sum[
f=DeleteCases[Eigenvalues[SS[c]],0];
(f/dtot[]^2).Log[f/dim[c]],{c,obs}
]


Unprotect[Abs,Conjugate,Power,Times,Sqrt,Im,Re];
Abs[\[Phi][a_,b_,c_][d_][e_,f_]]:=1;
Conjugate[\[Phi][a_,b_,c_][d_][e_,f_]]:=1/\[Phi][a,b,c][d][e,f];

Abs[\[Phi][a_,b_][c_]]:=1;
Conjugate[\[Phi][a_,b_][c_]]:=1/\[Phi][a,b][c];

Abs[\[Zeta][a_,b_,c_][d_][e_,f_]]:=1;
Conjugate[\[Zeta][a_,b_,c_][d_][e_,f_]]:=\[Zeta][a,b,c][d][e,f];
\[Zeta][a_,b_,c_][d_][e_,f_]^m_Integer/;(m<0||m>1):=\[Zeta][a,b,c][d][e,f]^Mod[m,2]

Abs[\[Zeta][a_,b_][c_]]:=1;
Conjugate[\[Zeta][a_,b_][c_]]:=\[Zeta][a,b][c];
\[Zeta][a_,b_][c_]^m_Integer/;(m<0||m>1):=\[Zeta][a,b][c]^Mod[m,2]
Abs[\[CurlyPhi][x_Integer][a_,b_,c_][d_][e_,f_]]:=1
Conjugate[\[CurlyPhi][x_Integer][a_,b_,c_][d_][e_,f_]]:=\[CurlyPhi][x][a,b,c][d][e,f]^-1
\[CurlyPhi][x_Integer][a_,b_,c_][d_][e_,f_]^m_Integer/;(m<0||m>=x):=\[CurlyPhi][x][a,b,c][d][e,f]^Mod[m,x]

Abs[\[CurlyPhi][x_Integer][a_,b_][c_]]:=1
Conjugate[\[CurlyPhi][x_Integer][a_,b_][c_]]:=\[CurlyPhi][x][a,b][c]^-1
\[CurlyPhi][x_Integer][a_,b_][c_]^m_Integer/;(m<0||m>=x):=\[CurlyPhi][x][a,b][c]^Mod[m,x]

Conjugate[Re0[a_,b_,c_][d_][e_,f_]]:=Re0[a,b,c][d][e,f];
Re[Re0[a_,b_,c_][d_][e_,f_]]:=Re0[a,b,c][d][e,f];
Im[Re0[a_,b_,c_][d_][e_,f_]]:=0;
Abs[Re0[a_,b_,c_][d_][e_,f_]]:=Sign[Re0[a,b,c][d][e,f]];
Conjugate[Re0[a_,b_][c_]]:=Re0[a,b][c];
Abs[Re0[a_,b_][c_]]:=Sign[Re0[a,b][c]];
Re[Re0[a_,b_][c_]]:=Re0[a,b][c];
Im[Re0[a_,b_][c_]]:=0;

Conjugate[U[a_,b_][c_]]/;V[a,b][c]==1:=1/U[a,b][c]

(*Abs[U[a_,b_][c_]]/;V[a,b][c]==1:=1;*)

Protect[Abs,Conjugate,Power,Times,Sqrt];
