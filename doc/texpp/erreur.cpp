\begin{flushleft}\ttfamily\upshape\parindent 0pt
~\\
function~gen\_{}round\_{}error(x:gen\_{}float)~:~real~=~~\\
~~~~~~~~~abs\_{}real(float\_{}value(x)~$-$~exact\_{}value(x))~\\
~\\
function~gen\_{}relative\_{}error(x:gen\_{}float)~:~real~=~\\
~~~~~~~~~abs\_{}real(float\_{}value(x)~$-$~exact\_{}value(x))~\\
~~~~~~~~~/exact\_{}value(x)~\\
~\\
function~gen\_{}total\_{}error(x:gen\_{}float)~:~real~=~\\
~~~~~~~~~abs\_{}real(float\_{}value(x)$-$model\_{}value(x))~\\
\end{flushleft}