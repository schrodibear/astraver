\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
parameter~add\_{}gen\_{}float~:~~\\
f:float\_{}format~$-$>~m:mode~$-$>~~\\
x:gen\_{}float~$-$>~y:gen\_{}float~$-$>~~\\
\{~\}~\\
gen\_{}float~\\
\{~\\
exact\_{}value(result)=exact\_{}value(x)+exact\_{}value(y)~~\\
and~\\
model\_{}value(result)=model\_{}value(x)+model\_{}value(y)~\\
and~\\
is\_{}nan(x)~or~is\_{}nan(y)~$-$>~is\_{}nan(result)~\\
~\\
~\\
~\\
\end{flushleft}