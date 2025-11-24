package com.face.secure.service;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.opencv.core.CvType;
import org.opencv.core.Mat;
import org.opencv.core.MatOfRect;
import org.opencv.core.Rect;
import org.opencv.core.Size;
import org.opencv.face.LBPHFaceRecognizer;
import org.opencv.imgcodecs.Imgcodecs;
import org.opencv.imgproc.Imgproc;
import org.opencv.objdetect.CascadeClassifier;

public class ModelTrainingService {
    
    private final CascadeClassifier faceDetector;
    private final File datasetDirectory;
    private final Path modelPath;
    
    public ModelTrainingService() {
        this(new File("E:/dataset"), Paths.get("E:/face.yml"));
    }

    public ModelTrainingService(File datasetDirectory, Path modelPath) {
        this.datasetDirectory = datasetDirectory;
        this.modelPath = modelPath;
        this.faceDetector = new CascadeClassifier(resolveCascadePath());
    }

    public List<Rect> detectFaces(Mat image) {
        MatOfRect faces = new MatOfRect();
        faceDetector.detectMultiScale(image, faces, 1.1, 3, 0, new Size(30, 30), new Size());
        for (Rect face : faces.toArray()) {
            Imgproc.rectangle(image, face, new org.opencv.core.Scalar(0, 255, 0), 2);
        }
        return List.of(faces.toArray());
    }

    private boolean isRectValid(Rect rect, Mat mat) {
        return rect.width > 50 && rect.height > 50 && rect.x >= 0 && rect.y >= 0;
    }

    public void trainFaceRecognizer() {
        //AQUI você deve adicionar o seu caminho para o dataset
        File[] labelDirs = datasetDirectory.listFiles(File::isDirectory);

        List<Mat> images = new ArrayList<>();
        List<Integer> labels = new ArrayList<>();

        for (File labelDir : labelDirs) {
            int label = Integer.parseInt(labelDir.getName());
            File[] imageFiles = labelDir.listFiles((dir, name) -> name.endsWith(".png"));


            if (imageFiles == null || imageFiles.length == 0) {
                System.err.println("Nenhuma imagem encontrada no diretório: " + labelDir.getAbsolutePath());
                continue;
            }

            int maxLength = String.valueOf(imageFiles.length).length();
            for (int i = 0; i < imageFiles.length; i++) {
                File oldFile = imageFiles[i];
                String newFileName = String.format("%s/%0" + maxLength + "d.png",
                        labelDir.getAbsolutePath(), i + 1);
                File newFile = new File(newFileName);

                if (!oldFile.renameTo(newFile)) {
                    System.err.println("Erro ao renomear arquivo: " + oldFile.getName());
                }
            }

            imageFiles = labelDir.listFiles((dir, name) -> name.endsWith(".png"));

            for (File imageFile : imageFiles) {
                Mat image = Imgcodecs.imread(imageFile.getAbsolutePath());

                if (image.empty()) {
                    System.err.println("Falha ao carregar a imagem: " + imageFile.getAbsolutePath());
                    continue;
                }
                List<Rect> faces = detectFaces(image);

                for (Rect face : faces) {
                    if (isRectValid(face, image)) {
                        Mat faceImage = new Mat(image, face);

                        if (faceImage.rows() > 0 && faceImage.cols() > 0) {
                            Mat resizedImage = new Mat();
                            Imgproc.resize(faceImage, resizedImage, new Size(150, 150));
                            Imgproc.cvtColor(resizedImage, resizedImage, Imgproc.COLOR_BGR2GRAY);
                            images.add(resizedImage);
                            labels.add(label);
                        } else {
                            System.err.println("A matriz faceImage está vazia ou com dimensões inválidas.");
                        }
                    } else {
                        System.err.println("Rect inválido para a imagem: " + imageFile.getAbsolutePath());
                    }
                }
            }
        }

        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        Mat labelsMat = new Mat(labels.size(), 1, CvType.CV_32SC1);
        for (int i = 0; i < labels.size(); i++) {
            labelsMat.put(i, 0, labels.get(i));
        }
        faceRecognizer.train(images, labelsMat);
        faceRecognizer.save(modelPath.toString());
    }

    public void addNewDataToModel() {
        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        //AQUI você deve adicionar o seu caminho para o modelo
        faceRecognizer.read(modelPath.toString());

        File[] labelDirs = datasetDirectory.listFiles(File::isDirectory);

        List<Mat> images = new ArrayList<>();
        List<Integer> labels = new ArrayList<>();

        for (File labelDir : labelDirs) {
            int label = Integer.parseInt(labelDir.getName());
            File[] imageFiles = labelDir.listFiles((dir, name) -> name.endsWith(".png"));
            int maxLength = String.valueOf(imageFiles.length).length();
            for (int i = 0; i < imageFiles.length; i++) {
                File oldFile = imageFiles[i];
                String newFileName = String.format("%s/%0" + maxLength + "d.png",
                        labelDir.getAbsolutePath(), i + 1);
                File newFile = new File(newFileName);

                if (!oldFile.renameTo(newFile)) {
                    System.err.println("Erro ao renomear arquivo: " + oldFile.getName());
                }
            }
            imageFiles = labelDir.listFiles((dir, name) -> name.endsWith(".png"));

            for (File imageFile : imageFiles) {
                Mat image = Imgcodecs.imread(imageFile.getAbsolutePath(), Imgcodecs.IMREAD_GRAYSCALE);
                if (!image.empty()) {
                    images.add(image);
                    labels.add(label);
                }
            }
        }

        Mat labelsMat = new Mat(labels.size(), 1, CvType.CV_32SC1);
        for (int i = 0; i < labels.size(); i++) {
            labelsMat.put(i, 0, labels.get(i));
        }

        faceRecognizer.update(images, labelsMat);
        
        //AQUI você deve adicionar o seu caminho para o modelo
        faceRecognizer.save(modelPath.toString());
    }

    private static String resolveCascadePath() {
        URL resource = ModelTrainingService.class.getClassLoader().getResource("haarcascade_frontalface_default.xml");
        if (resource == null) {
            throw new IllegalStateException("Não foi possível localizar o arquivo haarcascade_frontalface_default.xml nos recursos.");
        }
        try {
            return Paths.get(resource.toURI()).toFile().getAbsolutePath();
        } catch (URISyntaxException e) {
            throw new IllegalStateException("Falha ao resolver o caminho do classificador Haar.", e);
        }
    }
}
