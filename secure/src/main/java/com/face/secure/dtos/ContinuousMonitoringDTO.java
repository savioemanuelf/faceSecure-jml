package com.face.secure.dtos;

public class ContinuousMonitoringDTO {
    
    private /*@ spec_public @*/ int minutes;
    private /*@ spec_public @*/ int timeLimit;

    //@ public invariant minutes >= 0;
    //@ public invariant timeLimit >= 0;

    public ContinuousMonitoringDTO() {
    }

    /*@
      @ public normal_behavior
      @   requires minutes >= 0;
      @   requires timeLimit >= 0;
      @   ensures this.minutes == minutes;
      @   ensures this.timeLimit == timeLimit;
      @*/
    public ContinuousMonitoringDTO(int minutes, int timeLimit) {
        this.minutes = minutes;
        this.timeLimit = timeLimit;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.minutes;
      @*/
    public /*@ pure @*/ int getMinutes() {
        return minutes;
    }

    /*@
      @ public normal_behavior
      @   requires minutes >= 0;
      @   assignable this.minutes;
      @   ensures this.minutes == minutes;
      @*/
    public void setMinutes(int minutes) {
        this.minutes = minutes;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.timeLimit;
      @*/
    public /*@ pure @*/ int getTimeLimit() {
        return timeLimit;
    }

    /*@
      @ public normal_behavior
      @   requires timeLimit >= 0;
      @   assignable this.timeLimit;
      @   ensures this.timeLimit == timeLimit;
      @*/
    public void setTimeLimit(int timeLimit) {
        this.timeLimit = timeLimit;
    }
}