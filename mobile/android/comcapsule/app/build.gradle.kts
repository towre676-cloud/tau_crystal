plugins {
  id("com.android.application")
  kotlin("android")
}

android {
  namespace = "com.capsule"
  compileSdk = 34

  defaultConfig {
    applicationId = "io.capsule.seal"
    minSdk = 26
    targetSdk = 34
    versionCode = 9
    versionName = "0.0.9"
  }

  buildTypes {
    debug { }
    release {
      isMinifyEnabled = false
      signingConfig = signingConfigs.getByName("debug")
    }
  }

  compileOptions {
    sourceCompatibility = JavaVersion.VERSION_17
    targetCompatibility = JavaVersion.VERSION_17
  }
  kotlinOptions { jvmTarget = "17" }
}

dependencies {
  implementation("androidx.core:core-ktx:1.13.1")
  implementation("androidx.appcompat:appcompat:1.7.0")
}
