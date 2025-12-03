package com.face.secure.dtos;

public class DetectFacesDTO {
    
    /*@ spec_public nullable @*/
    private String name;

    /*@ spec_public nullable @*/
    private String confidence;

    /*@ spec_public @*/
    private boolean faceDetected;

    /*@ pure nullable @*/
    public String getName() {
        return name;
    }

    /*@ 
      @ public normal_behavior
      @   assignable this.name;
      @   ensures this.name == name;
      @*/
    public void setName(String name) {
        this.name = name;
    }

    /*@ pure nullable @*/
    public String getConfidence() {
        return confidence;
    }

    /*@ 
      @ public normal_behavior
      @   assignable this.confidence;
      @   ensures this.confidence == confidence;
      @*/
    public void setConfidence(String confidence) {
        this.confidence = confidence;
    }

    /*@ pure @*/
    public boolean isFaceDetected() {
        return faceDetected;
    }

    /*@ 
      @ public normal_behavior
      @   assignable this.faceDetected;
      @   ensures this.faceDetected == faceDetected;
      @*/
    public void setFaceDetected(boolean faceDetected) {
        this.faceDetected = faceDetected;
    }

    public DetectFacesDTO() {
    }

    /*@
      @ public normal_behavior
      @   ensures this.name == name;
      @   ensures this.confidence == confidence;
      @   ensures this.faceDetected == faceDetected;
      @*/
    public DetectFacesDTO(String name, String confidence, boolean faceDetected) {
        this.name = name;
        this.confidence = confidence;
        this.faceDetected = faceDetected;
    }
}