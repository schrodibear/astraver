\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\textbf{predicate}~~\\
overflow\_{}value(f:float\_{}format,m:mode,x:gen\_{}float)=~~\\
m~=~down~$-$>~~\\
~~~float\_{}sign(x)~=~Negative~$-$>~is\_{}infinite(x)~\\
~~~and~\\
~~~float\_{}sign(x)~=~Positive~$-$>~is\_{}finite(x)~and~\\
~~~~~~~~~~~~~~~~~~~float\_{}value(x)~=~max\_{}gen\_{}float(f)~~\\
and~\\
m~=~up~$-$>~~\\
~~~float\_{}sign(x)~=~Negative~$-$>~is\_{}finite(x)~and~~\\
~~~~~~~~~~~~~~~~~~~float\_{}value(x)~=~$-$~max\_{}gen\_{}float(f)~~\\
~~~and~\\
~~~float\_{}sign(x)~=~Positive~$-$>~is\_{}infinite(x)~~~\\
~\\
~\\
\end{flushleft}