\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
parameter~gen\_{}float\_{}of\_{}real~:~\\
f:float\_{}format~$-$>~m:mode~$-$>~x:real~$-$>~\\
\{~\}~\\
gen\_{}float~\\
\{~~\\
no\_{}overflow(f,m,x)~$-$>~is\_{}finite(result)~and~~\\
~~~~~~~~~~~float\_{}value(result)~=~round\_{}float(f,m,x)~\\
~~~~~~~~~~~and~sign\_{}zero\_{}result(m,result)~\\
and~~\\
not~no\_{}overflow(f,m,x)~$-$>~same\_{}sign\_{}real(result,x)~~\\
~~~~~~~~~~~and~overflow\_{}value(f,m,result)~\\
and~~\\
exact\_{}value(result)~=~x~and~\\
model\_{}value(result)~=~x~\\
\}~\\
\end{flushleft}