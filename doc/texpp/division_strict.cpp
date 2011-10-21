\begin{flushleft}\ttfamily\upshape\parindent 0pt
parameter~div\_{}gen\_{}float~:~~\\
f:float\_{}format~$-$>~m:mode~$-$>~~\\
x:gen\_{}float~$-$>~y:gen\_{}float~$-$>~~\\
\{~float\_{}value(y)~<>~0.0~~\\
~~and~~\\
~~no\_{}overflow(f,m,float\_{}value(x)/float\_{}value(y))~\}~\\
gen\_{}float~\\
\{float\_{}value(result)~=~~\\
~~~~~~round\_{}float(f,m,float\_{}value(x)/float\_{}value(y))~\\
~and~~\\
~exact\_{}value(result)~=~exact\_{}value(x)/exact\_{}value(y)~\\
~and~~\\
~model\_{}value(result)~=~model\_{}value(x)/model\_{}value(y)~\\
\}~\\
\end{flushleft}