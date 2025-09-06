Param([string]$Out,[string]$Text)
Add-Type -AssemblyName System.Drawing
$w=1280;$h=720
$bmp=New-Object Drawing.Bitmap $w,$h
$g=[Drawing.Graphics]::FromImage($bmp)
$bg=New-Object Drawing.SolidBrush ([Drawing.Color]::FromArgb(11,15,26))
$g.FillRectangle($bg,0,0,$w,$h)
$font=New-Object Drawing.Font("Consolas",36,[Drawing.FontStyle]::Regular,[Drawing.GraphicsUnit]::Pixel)
$fg=New-Object Drawing.SolidBrush ([Drawing.Color]::FromArgb(230,237,243))
$fmt=New-Object Drawing.StringFormat
$fmt.Alignment=[Drawing.StringAlignment]::Center
$fmt.LineAlignment=[Drawing.StringAlignment]::Center
$g.TextRenderingHint=[System.Drawing.Text.TextRenderingHint]::AntiAlias
$g.DrawString($Text,$font,$fg,(New-Object Drawing.RectangleF(0,0,$w,$h)),$fmt)
$bmp.Save($Out,[Drawing.Imaging.ImageFormat]::Png)
