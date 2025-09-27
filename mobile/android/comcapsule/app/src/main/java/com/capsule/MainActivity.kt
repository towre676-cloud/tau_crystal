package com.capsule

import android.app.Activity
import android.os.Bundle
import android.util.Log
import android.widget.TextView
import android.view.ViewGroup
import android.view.Gravity
import android.Manifest
import android.content.pm.PackageManager
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import android.media.AudioFormat
import android.media.AudioRecord
import android.media.MediaRecorder
import java.io.File
import java.io.FileOutputStream
import java.io.FileDescriptor
import java.lang.reflect.Method
import java.security.MessageDigest
import org.json.JSONObject

class MainActivity : Activity() {
  private var didCapture = false

  private fun provenance(tag: String) {
    try {
      val p = packageManager.getPackageInfo(packageName, 0)
      Log.i("Capsule", "[$tag] pkg=$packageName code=${p.longVersionCode} name=${p.versionName} cls=${this::class.java.name}")
    } catch (e: Exception) {
      Log.w("Capsule", "[$tag] package info lookup failed", e)
    }
  }

  override fun onCreate(savedInstanceState: Bundle?) {
    super.onCreate(savedInstanceState)
    provenance("onCreate")

    val tv = TextView(this).apply {
      text = "Capsule — witness zero\n\nRecording 5s test…"
      textSize = 18f
      gravity = Gravity.CENTER
      layoutParams = ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT)
    }
    setContentView(tv)

    // Request mic permission if needed
    if (ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED) {
      ActivityCompat.requestPermissions(this, arrayOf(Manifest.permission.RECORD_AUDIO), 1001)
    }
  }

  override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
    super.onRequestPermissionsResult(requestCode, permissions, grantResults)
    if (requestCode == 1001 && grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
      Log.i("Capsule", "[perm] RECORD_AUDIO=true (granted via prompt)")
      // Defer actual capture to onResume to ensure we’re foreground
    } else {
      Log.w("Capsule", "[perm] RECORD_AUDIO=false; skipping capture")
    }
  }

  override fun onResume() {
    super.onResume()
    provenance("onResume")
    val have = (checkSelfPermission(Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED)
    Log.i("Capsule", "[perm] RECORD_AUDIO=$have")
    if (have && !didCapture) {
      didCapture = true
      // Post to message queue to ensure UI is drawn before we do work
      window?.decorView?.post { captureOnce() }
    }
  }

  private fun fsync(fd: FileDescriptor) {
    // Reflective fsync to harden writes; safe no-op if unavailable
    try {
      val m: Method = FileDescriptor::class.java.getMethod("sync")
      m.invoke(fd)
    } catch (_: Throwable) { /* ignore */ }
  }

  private fun captureOnce() {
    val sampleRate = 16_000
    val channelConfig = AudioFormat.CHANNEL_IN_MONO
    val audioFormat = AudioFormat.ENCODING_PCM_16BIT
    val seconds = 5
    val bytesPerSample = 2
    val targetBytes = sampleRate * seconds * bytesPerSample

    val minBuf = AudioRecord.getMinBufferSize(sampleRate, channelConfig, audioFormat)
    val bufSize = maxOf(minBuf, 4096)
    val audio = AudioRecord(MediaRecorder.AudioSource.MIC, sampleRate, channelConfig, audioFormat, bufSize)

    val outRaw = File(filesDir, "witness_${System.currentTimeMillis()}_${sampleRate}Hz.pcm")
    var fos: FileOutputStream? = null
    var bytesWritten = 0
    val md = MessageDigest.getInstance("SHA-256")

    try {
      audio.startRecording()
      fos = FileOutputStream(outRaw)
      val buf = ByteArray(bufSize)

      while (bytesWritten < targetBytes) {
        val toRead = minOf(buf.size, targetBytes - bytesWritten)
        val n = audio.read(buf, 0, toRead)
        if (n > 0) {
          fos.write(buf, 0, n)
          md.update(buf, 0, n)
          bytesWritten += n
        } else if (n == 0) {
          // brief yield
          Thread.sleep(5)
        } else {
          Log.w("Capsule", "[capture] audio.read returned $n; stopping early")
          break
        }
      }

      fos.flush()
      fsync(fos.fd)

      val hash = md.digest().joinToString("") { "%02x".format(it) }
      Log.i("Capsule", "[capture] wrote=${bytesWritten}B pcm=${outRaw.name} sha256=$hash")

      // Sidecar JSON (guarded)
      try {
        val p = packageManager.getPackageInfo(packageName, 0)
        val meta = JSONObject().apply {
          put("package", packageName)
          put("versionName", p.versionName)
          put("versionCode", p.longVersionCode)
          put("class", this@MainActivity::class.java.name)
          put("sampleRateHz", sampleRate)
          put("channels", 1)
          put("encoding", "PCM_16BIT")
          put("durationSec", seconds)
          put("bytes", bytesWritten)
          put("sha256", hash)
          put("file", outRaw.name)
          put("ts", System.currentTimeMillis())
        }
        val sidecar = File(outRaw.parentFile, outRaw.nameWithoutExtension + ".json")
        FileOutputStream(sidecar).use { it.write(meta.toString().toByteArray(Charsets.UTF_8)) }
        Log.i("Capsule", "[sidecar] ${sidecar.name} written")
      } catch (e: Exception) {
        Log.e("Capsule", "[sidecar] write failed", e)
      }
    } catch (e: SecurityException) {
      Log.e("Capsule", "[capture] mic permission error", e)
    } catch (e: Exception) {
      Log.e("Capsule", "[capture] failed", e)
    } finally {
      try { fos?.close(); } catch (_: Exception) {}
      try { audio.stop(); } catch (_: Exception) {}
      try { audio.release(); } catch (_: Exception) {}
    }
  }
}
