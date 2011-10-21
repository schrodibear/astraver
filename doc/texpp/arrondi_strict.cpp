\begin{flushleft}\ttfamily\upshape\parindent 0pt
parameter~gen\_{}float\_{}of\_{}real~:~\\
f:float\_{}format~$-$>~m:mode~$-$>~x:real~$-$>~\\
\{~no\_{}overflow(f,m,x)~~\\
\}~\\
gen\_{}float~\\
\{~~\\
float\_{}value(result)~=~round\_{}float(f,m,x)~\\
and~~\\
exact\_{}value(result)~=~x~~\\
and~\\
model\_{}value(result)~=~x~\\
\}~\\
\end{flushleft}