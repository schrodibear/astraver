\begin{flushleft}\ttfamily\upshape\parindent 0pt
~\\
\textbf{predicate}~sign\_{}zero\_{}result(m:mode,x:gen\_{}float)~=~~\\
~~~~~~float\_{}value(x)~=~0.0~$-$>~~\\
~~~~~~(m~=~down~$-$>~float\_{}sign(x)~=~Negative)~~\\
~~~~~~~and~~\\
~~~~~~(m~<>~down~$-$>~float\_{}sign(x)~=~Positive)~~\\
~\\
\textbf{axiom}~finite\_{}sign~:~forall~x:gen\_{}float.~\\
~~~~~~is\_{}finite(x)~and~float\_{}value(x)~<>~0.0~$-$>~~\\
~~~~~~same\_{}sign\_{}real(x,float\_{}value(x))~\\
\end{flushleft}