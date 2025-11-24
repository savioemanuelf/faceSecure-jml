package com.face.secure.service;

import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

public class ContinuousMonitoringService {

    private final FaceRecognitionService faceRecognitionService;

    public ContinuousMonitoringService(FaceRecognitionService faceRecognitionService) {
        this.faceRecognitionService = faceRecognitionService;
    }

    private int timePassed = 0;

    public boolean startMonitoring(int minutes, int timeLimit) {
        long timeLimitMin = timeLimit * 60000;
        long startTime = System.currentTimeMillis();
        boolean[] stillAllTime = {true};
        AtomicBoolean stillAllTime2 = new AtomicBoolean(true);
        
        ScheduledExecutorService scheduler = Executors.newScheduledThreadPool(1);

        

            Runnable task = new Runnable() {
                public void run() {
                    try {
                        System.out.println("Checking for faces");
                        if (faceRecognitionService.detectFaces()) {
                            System.out.println("Face detected");
                            timePassed = 0;
                        } else {
                            scheduler.shutdown();
                            stillAllTime[0] = false;
                            stillAllTime2.set(false);
                            System.out.println("Face not detected");
                        }
                    } catch (Exception e) {
                        e.printStackTrace();
                        scheduler.shutdown();
                        stillAllTime[0] = false;
                        stillAllTime2.set(false);
                    }
                }
            };
            scheduler.scheduleAtFixedRate(task, 0, minutes, TimeUnit.MINUTES);
            
            while(System.currentTimeMillis() - startTime < timeLimitMin){
                try {
                    if(stillAllTime2.get()){    
                        Thread.sleep(1000);
                        timePassed++;
                        System.out.println("Time passed: " + timePassed + " seconds");
                    }else{
                        scheduler.shutdown();
                        break;
                    }
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
        scheduler.shutdown();
        if(stillAllTime2.get()){
            System.out.println("ta verdade");
        }else{
            System.out.println("ta falso");
        }
        return stillAllTime2.get();
    }
}
