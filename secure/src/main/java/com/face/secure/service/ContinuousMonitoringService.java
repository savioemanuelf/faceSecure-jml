package com.face.secure.service;

import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

public class ContinuousMonitoringService {

    //@ public invariant faceRecognitionService != null;
    //@ public invariant timePassed >= 0;

    private final /*@ spec_public non_null @*/ FaceRecognitionService faceRecognitionService;

    /*@ 
      @ public normal_behavior
      @   requires faceRecognitionService != null;
      @   ensures this.faceRecognitionService == faceRecognitionService;
      @   ensures this.timePassed == 0;
      @*/
    public ContinuousMonitoringService(FaceRecognitionService faceRecognitionService) {
        this.faceRecognitionService = faceRecognitionService;
    }

    private /*@ spec_public @*/ int timePassed = 0;

    /*@ 
      @ public behavior
      @   requires true; 
      @   ensures \result == true || \result == false;
      @   ensures \result ==> (timePassed == 0); 
      @   assignable timePassed; 
      @   signals_only java.lang.RuntimeException;
      @*/
    public boolean performCheck() {
        boolean detected = faceRecognitionService.detectFaces();
        if (detected) {
            timePassed = 0;
            return true;
        } else {
            return false;
        }
    }

    /*@ 
      @ public behavior
      @   requires minutes > 0; 
      @   requires timeLimit > 0;
      @   ensures \result == true || \result == false;
      @   signals_only java.lang.RuntimeException;
      @*/
    public /*@ skipesc @*/ boolean startMonitoring(int minutes, int timeLimit) {
        long timeLimitMin = timeLimit * 60000L;
        long startTime = System.currentTimeMillis();
        AtomicBoolean monitoringActive = new AtomicBoolean(true);
        ScheduledExecutorService scheduler = Executors.newScheduledThreadPool(1);

        Runnable task = () -> {
            try {
                if (performCheck()) {
                    System.out.println("Face detected");
                } else {
		    System.out.println("Face not detected");
                    monitoringActive.set(false);
                    scheduler.shutdown();
		}
            } catch (Exception e) {
                e.printStackTrace();
            }
        };
        
        scheduler.scheduleWithFixedDelay(task, 0, 5, TimeUnit.SECONDS);

        /*@
          @ loop_invariant timePassed >= 0;
          @ loop_invariant System.currentTimeMillis() >= startTime;
          @ loop_modifies timePassed;
          @*/
	while (System.currentTimeMillis() - startTime < timeLimitMin) {
            try {
                if (monitoringActive.get()) {
                    Thread.sleep(1000);
                    timePassed++; 
                    System.out.println("Time passed: " + timePassed + " seconds");
                } else {
                    scheduler.shutdown();
                    break;
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        scheduler.shutdown();
        
        if (monitoringActive.get()) {
            System.out.println("Monitoramento finalizado pelo tempo limite.");
        } else {
            System.out.println("Monitoramento interrompido: Nenhuma face detectada.");
        }
        return monitoringActive.get();
    }
}
