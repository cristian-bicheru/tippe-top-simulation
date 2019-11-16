import Jama.*;
import Jama.examples.*;
import Jama.test.*;
import Jama.util.*;

import peasy.*;

int width = 1600;
int height = 1000;

//camera values
PeasyCam cam;
float cx = 0;
float cy = 0;
float cz = 0;
float ctheta = 0;
float cphi = 0;
float cpsi = 0;

float fps = 60;
int stepsPerFrame = 1000;
//int stepsPerFrame = 1000;
float dt = 1/(fps*stepsPerFrame);

//font
PFont tahoma;

//tippe texture
PImage img, img2, img3;

//tippe top
Tippe top;

boolean useDormandPrince = true; //else RK4, dormand prince is sketchy
boolean debug = false;
boolean drawVectors = true;

float vRAD = 0.75;
float vLENGTH = 10;
float vPOINTY = 4;
float vRAD2 = 2;
float vdx, vdy, vdz; // global so that subsequent function calls have access

void drawVector(float ox, float oy, float oz, float x, float y, float z, float delta, float cr, float cg, float cb, PVector referenceVector) {
  PVector temp = new PVector(x, y, z);
  float ratio = referenceVector.mag()/temp.mag(), r, l, p, r2, dphi, dtheta;
  if (ratio > 0) {
    ratio = log(ratio+1)/log(2);
  } // else linear
  pushMatrix();
  translate(ox, oy, oz);
  dtheta = atan2(z, x);
  dphi = atan2(y, sqrt(x*x+z*z))+PI/2.0;
  rotateY(dtheta);
  rotateZ(dphi);
  
  //rotateX(PI/2.0);
  r = vRAD*ratio;
  l = vLENGTH*ratio;
  p = vPOINTY*ratio;
  r2 = vRAD2*ratio;
  vdx = (l+p)*sin(dphi)*cos(dtheta);
  vdz = (l+p)*sin(dphi)*sin(dtheta);
  vdy = (l+p)*cos(dphi);
  beginShape(QUAD_STRIP);
  fill(cr, cg, cb);
  for(float theta = 0.0; theta <= TWO_PI*1.1; theta += delta) {
      x = r * cos(theta);
      z = r * sin(theta);
      vertex(x, 0, z);
      vertex(x, l, z);
  }
  endShape(CLOSE);
  beginShape();
  for(float theta = 0.0; theta <= TWO_PI; theta += delta) {
      x = r * cos(theta);
      z = r * sin(theta);
      vertex(x, 0, z);
  }
  endShape(CLOSE);
  beginShape(TRIANGLES); 
  for(float theta = 0.0; theta <= TWO_PI; theta += delta) {
      x = r2 * cos(theta);
      z = r2 * sin(theta);
      vertex(x, l, z);
      vertex(0, l+p, 0);
      x = r2 * cos(theta+delta);
      z = r2 * sin(theta+delta);
      vertex(x, l, z);
  }
  endShape(CLOSE);
  beginShape();
  for(float theta = 0.0; theta <= TWO_PI; theta += delta) {
      x = r2 * cos(theta);
      z = r2 * sin(theta);
      vertex(x, l, z);
  }
  endShape(CLOSE);  
  popMatrix();
  noFill();
  fill(255,255,255,0);
}

double[][] evolveSecondDerivatives(float theta, float phi, float psi, float R, float alpha, float m, float mu, float i1, float i3, float g, float dtheta, float dphi, float dpsi, float dx, float dy) {
  PVector a, Va, n, axn;
  float sinTheta, cosTheta, sinPhi, cosPhi;
  PVector k = new PVector(0, 0, 1);
  double[][] Mf = new double[6][6];
  double[][] Bf = new double[6][1];
  boolean failed = false, singular = false;
  Matrix M, B, X = new Matrix(new double[][] {{}}), M1;
  
  sinTheta = sin(theta);
  cosTheta = cos(theta);
  sinPhi = sin(phi);
  cosPhi = cos(phi);
  a = new PVector(alpha*cosPhi*sinTheta, alpha*sinPhi*sinTheta, alpha*cosTheta-1).mult(R);
  Va = new PVector(dx-R*(dtheta*cosPhi+dpsi*sinPhi*sinTheta), dy-R*(dtheta*sinPhi-dpsi*cosPhi*sinTheta), 0);
  n = (Va.normalize().mult(mu)).sub(k);
  axn = a.cross(n);
  Mf[0][1] = m;
  Mf[1][2] = m;
  Mf[0][0] = n.x;
  Mf[1][0] = n.y;
  Mf[2][0] = n.z;
  Mf[3][0] = axn.x;
  Mf[4][0] = axn.y;
  Mf[5][0] = axn.z;
  Mf[0][3] = R*alpha*m*sinPhi*sinTheta;
  Mf[0][4] = -R*alpha*m*cosPhi*cosTheta;
  Mf[1][3] = -R*alpha*m*cosPhi*sinTheta;
  Mf[1][4] = -R*alpha*m*sinPhi*cosTheta;
  Mf[2][4] = R*alpha*m*sinTheta;
  Mf[3][3] = (i3-i1)*cosPhi*cosTheta*sinTheta;
  Mf[3][4] = -i1*sinPhi;
  Mf[3][5] = i3*cosPhi*sinTheta;
  Mf[4][3] = (i3-i1)*sinPhi*cosTheta*sinTheta;
  Mf[4][4] = i1*cosPhi;
  Mf[4][5] = i3*sinPhi*sinTheta;
  Mf[5][3] = i1*pow(sinTheta, 2)+i3*pow(cosTheta, 2);
  Mf[5][5] = i3*cosTheta;
  M = new Matrix(Mf);
  Bf[0][0] = -R*alpha*m*((pow(dphi, 2)+pow(dtheta, 2))*cosPhi*sinTheta+2*dphi*dtheta*sinPhi*cosTheta);
  Bf[1][0] = -R*alpha*m*((pow(dphi, 2)+pow(dtheta, 2))*sinPhi*sinTheta-2*dphi*dtheta*cosPhi*cosTheta);
  Bf[2][0] = -R*alpha*m*pow(dtheta, 2)*cosTheta-m*g;
  Bf[3][0] = ((i3-i1)*dphi*cosTheta+i3*dpsi)*(dphi*sinPhi*sinTheta-dtheta*cosPhi*cosTheta)+dphi*dtheta*cosPhi*(i1*pow(cosTheta, 2)+i3*pow(sinTheta, 2));
  Bf[4][0] = -((i3-i1)*dphi*cosTheta+i3*dpsi)*(dphi*cosPhi*sinTheta+dtheta*sinPhi*cosTheta)+dphi*dtheta*sinPhi*(i1*pow(cosTheta, 2)+i3*pow(sinTheta, 2));
  Bf[5][0] = dtheta*sinTheta*(2*(i3-i1)*dphi*cosTheta+i3*dpsi);
  B = new Matrix(Bf);
  if (Mf[3][0] == 0 && Mf[3][1] == 0 && Mf[3][2] == 0 && Mf[3][3] == 0 && Mf[3][4] == 0) {
    M1 = M.getMatrix(new int[] {0, 1, 2, 4, 5}, new int[] {0, 1, 2, 4, 5});
    M.print(20, 20);
    M1.print(20, 20);
    try {
       X = M1.solve(B);
       singular = true;
    } catch (RuntimeException e) {
      println("singluar test case failure");
      failed = true;
    }
  }
  
  if ((Mf[4][0] == 0 && Mf[4][1] == 0 && Mf[4][2] == 0 && Mf[4][3] == 0 && Mf[4][4] == 0) || failed == true) {
    M1 = M.getMatrix(new int[] {0, 1, 2, 3, 5}, new int[] {0, 1, 2, 4, 5});
    try {
       X = M1.solve(B);
       singular = true;
    } catch (RuntimeException e) {
      println("failed to invert matrix");
      exit();
    }
  }
  
  if (singular == false) {
    X = M.solve(B);
  }

  if (debug == true) {
    println("MATRIX M");
    M.print(6, 6);
    println("MATRIX B");
    B.print(6,6);
    println("MATRIX X");
    X.print(6,6);
  }
  return X.getArray();
}

double[][] paperEquations(float theta, float phi, float psi, float R, float alpha, float m, float mu, float i1, float i3, float g, float dtheta, float dphi, float dpsi, float dx, float dy) {
  //double[][] ret;
  double N, ddx, ddy, ddphi, ddtheta, ddpsi;
  float sinTheta, cosTheta, sinPhi, cosPhi;
  sinTheta = sin(theta);
  cosTheta = cos(theta);
  sinPhi = sin(phi);
  cosPhi = cos(phi);
  N = (m*g*i1+m*R*alpha*(cosTheta*(i1*dphi*dphi*sinTheta*sinTheta+i1*dtheta*dtheta)-i3*dphi*dpsi*sinTheta*sinTheta))/(i1+m*R*R*alpha*alpha*sinTheta*sinTheta-m*R*R*alpha*sinTheta*(1-alpha*cosTheta)*mu*dx);
  ddx = (R*sinTheta/i1)*(dphi*dpsi*(i3*(1-alpha*cosTheta)-i1)+N*R*alpha*(1-alpha*cosTheta)-i1*alpha*(dtheta*dtheta+dphi*dphi*sinTheta*sinTheta));
  ddy = -((mu*N*dy)/(m*i1*i3))*(i1*i3+m*R*R*i3*(alpha-cosTheta)*(alpha-cosTheta)+m*R*R*i1*sinTheta*sinTheta)+(dpsi*dtheta*R/i1)*(i3*(alpha-cosTheta)+i1*cosTheta)-dphi*dx;
  ddphi = (i3*dtheta*dpsi-2*i1*dtheta*dphi*cosTheta-mu*N*dy*R*(alpha-cosTheta))/(i1*sinTheta);
  ddtheta = (sinTheta/i1)*(i1*dphi*dphi*cosTheta-i3*dpsi*dphi-R*alpha*N)+(R*mu*N*dx/i1)*(1-alpha*cosTheta);
  ddpsi = -(mu*N*dy*R*sinTheta)/i3;
  double[][] ret = {{N}, {ddx}, {ddy}, {ddphi}, {ddtheta}, {ddpsi}};
  return ret;
}

float[] evolve(float N, float theta, float phi, float psi, float R, float alpha, float m, float mu, float i1, float i3, float g, float dtheta, float dphi, float dpsi, float dx, float dy) {
  float[] ds = new float[11]; // N, dx, dy, dphi, dtheta, dpsi, ddx, ddy, ddphi, ddtheta, ddpsi
  double[][] secondDerivatives0;
  double[][] secondDerivatives1;
  double[][] secondDerivatives2;
  double[][] secondDerivatives3;
  float N1, dx1, dy1, dtheta1, dphi1, dpsi1;
  float N2, dx2, dy2, dtheta2, dphi2, dpsi2;
  float N3, dx3, dy3, dtheta3, dphi3, dpsi3;
  if (useDormandPrince == false) {
    // c0 = first order derivatives
    // k0 = secondDerviatives0
    secondDerivatives0 = evolveSecondDerivatives(theta, phi, psi, R, alpha, m, mu, i1, i3, g, dtheta, dphi, dpsi, dx, dy);
    // c1 = first order + h/2*k0
    N1 = (float) secondDerivatives0[0][0];
    dx1 = dx+(float) secondDerivatives0[1][0]*dt/2.0;
    dy1 = dy+(float) secondDerivatives0[2][0]*dt/2.0;
    dphi1 = dphi+(float) secondDerivatives0[3][0]*dt/2.0;
    dtheta1 = dtheta+(float) secondDerivatives0[4][0]*dt/2.0;
    dpsi1 = dpsi+(float) secondDerivatives0[5][0]*dt/2.0;
    // k1 = secondDerivatives1
    secondDerivatives1 = evolveSecondDerivatives(theta+dtheta*dt/2.0, phi+dphi*dt/2.0, psi+dpsi*dt/2.0, R, alpha, m, mu, i1, i3, g, dtheta1, dphi1, dpsi1, dx1, dy1);
    // c2 = first order +h/2*k1
    N2 = (float) secondDerivatives1[0][0];
    dx2 = dx+(float) secondDerivatives1[1][0]*dt/2.0;
    dy2 = dy+(float) secondDerivatives1[2][0]*dt/2.0;
    dphi2 = dphi+(float) secondDerivatives1[3][0]*dt/2.0;
    dtheta2 = dtheta+(float) secondDerivatives1[4][0]*dt/2.0;
    dpsi2 = dpsi+(float) secondDerivatives1[5][0]*dt/2.0;
    // k2 = secondDerivatives2
    secondDerivatives2 = evolveSecondDerivatives(theta+dtheta1*dt/2.0, phi+dphi1*dt/2.0, psi+dpsi1*dt/2.0, R, alpha, m, mu, i1, i3, g, dtheta2, dphi2, dpsi2, dx2, dy2);
    // c3 = first order +h*k2
    N3 = (float) secondDerivatives2[0][0];
    dx3 = dx+(float) secondDerivatives2[1][0]*dt;
    dy3 = dy+(float) secondDerivatives2[2][0]*dt;
    dphi3 = dphi+(float) secondDerivatives2[3][0]*dt;
    dtheta3 = dtheta+(float) secondDerivatives2[4][0]*dt;
    dpsi3 = dpsi+(float) secondDerivatives2[5][0]*dt;
    // k3 = secondDerivatives3
    secondDerivatives3 = evolveSecondDerivatives(theta+dtheta2*dt, phi+dphi2*dt, psi+dpsi2*dt, R, alpha, m, mu, i1, i3, g, dtheta3, dphi3, dpsi3, dx3, dy3);
    ds[0] = (N+2*N1+2*N2+N3)/6.0;
    ds[1] = (dx+2*dx1+2*dx2+dx3)*dt/6.0;
    ds[2] = (dy+2*dy1+2*dy2+dy3)*dt/6.0;
    ds[3] = (dphi+2*dphi1+2*dphi2+dphi3)*dt/6.0;
    ds[4] = (dtheta+2*dtheta1+2*dtheta2+dtheta3)*dt/6.0;
    ds[5] = (dpsi+2*dpsi1+2*dpsi2+dpsi3)*dt/6.0;
    ds[6] = (float) (secondDerivatives0[1][0]+2*secondDerivatives1[1][0]+2*secondDerivatives2[1][0]+secondDerivatives3[1][0])*dt/6.0;
    ds[7] = (float) (secondDerivatives0[2][0]+2*secondDerivatives1[2][0]+2*secondDerivatives2[2][0]+secondDerivatives3[2][0])*dt/6.0;
    ds[8] = (float) (secondDerivatives0[3][0]+2*secondDerivatives1[3][0]+2*secondDerivatives2[3][0]+secondDerivatives3[3][0])*dt/6.0;
    ds[9] = (float) (secondDerivatives0[4][0]+2*secondDerivatives1[4][0]+2*secondDerivatives2[4][0]+secondDerivatives3[4][0])*dt/6.0;
    ds[10] = (float) (secondDerivatives0[5][0]+2*secondDerivatives1[5][0]+2*secondDerivatives2[5][0]+secondDerivatives3[5][0])*dt/6.0;
    
  } else {
    double[][] secondDerivatives4;
    double[][] secondDerivatives5;
    //double[][] secondDerivatives6;
    float N4, dx4, dy4, dtheta4, dphi4, dpsi4;
    float N5, dx5, dy5, dtheta5, dphi5, dpsi5;
    //float N6, dx6, dy6, dtheta6, dphi6, dpsi6;
    secondDerivatives0 = evolveSecondDerivatives(theta, phi, psi, R, alpha, m, mu, i1, i3, g, dtheta, dphi, dpsi, dx, dy);
    // c1 = first order + h/5*k0
    N1 = (float) secondDerivatives0[0][0];
    dx1 = dx+(float) secondDerivatives0[1][0]*dt/5.0;
    dy1 = dy+(float) secondDerivatives0[2][0]*dt/5.0;
    dphi1 = dphi+(float) secondDerivatives0[3][0]*dt/5.0;
    dtheta1 = dtheta+(float) secondDerivatives0[4][0]*dt/5.0;
    dpsi1 = dpsi+(float) secondDerivatives0[5][0]*dt/5.0;
    // k1 = secondDerivatives1
    secondDerivatives1 = evolveSecondDerivatives(theta+dtheta*dt/5.0, phi+dphi*dt/5.0, psi+dpsi*dt/5.0, R, alpha, m, mu, i1, i3, g, dtheta1, dphi1, dpsi1, dx1, dy1);
    // c2 = first order +h*3/10*k1
    N2 = (float) secondDerivatives1[0][0];
    dx2 = dx+(float) (secondDerivatives0[1][0]*dt*3.0/40.0+secondDerivatives1[1][0]*dt*9.0/40.0);
    dy2 = dy+(float) (secondDerivatives0[2][0]*dt*3.0/40.0+secondDerivatives1[2][0]*dt*9.0/40.0);
    dphi2 = dphi+(float) (secondDerivatives0[3][0]*dt*3.0/40.0+secondDerivatives1[3][0]*dt*9.0/40.0);
    dtheta2 = dtheta+(float) (secondDerivatives0[4][0]*dt*3.0/40.0+secondDerivatives1[4][0]*dt*9.0/40.0);
    dpsi2 = dpsi+(float) (secondDerivatives0[5][0]*dt*3.0/40.0+secondDerivatives1[5][0]*dt*9.0/40.0);
    // k2 = secondDerivatives2
    secondDerivatives2 = evolveSecondDerivatives(theta+dtheta*dt*3.0/40.0+dtheta1*dt*9.0/40.0, phi+dphi*dt*3.0/40.0+dphi1*dt*9.0/40.0, psi+dpsi*dt*3.0/40.0+dpsi1*dt*9.0/40.0, R, alpha, m, mu, i1, i3, g, dtheta2, dphi2, dpsi2, dx2, dy2);
    // c3 = first order +h*4/5*k2
    N3 = (float) secondDerivatives2[0][0];
    dx3 = dx+(float) (secondDerivatives0[1][0]*dt*44.0/45.0-secondDerivatives1[1][0]*dt*56.0/15.0+secondDerivatives2[1][0]*dt*32.0/9.0);
    dy3 = dy+(float) (secondDerivatives0[2][0]*dt*44.0/45.0-secondDerivatives1[2][0]*dt*56.0/15.0+secondDerivatives2[2][0]*dt*32.0/9.0);
    dphi3 = dphi+(float) (secondDerivatives0[3][0]*dt*44.0/45.0-secondDerivatives1[3][0]*dt*56.0/15.0+secondDerivatives2[3][0]*dt*32.0/9.0);
    dtheta3 = dtheta+(float) (secondDerivatives0[4][0]*dt*44.0/45.0-secondDerivatives1[4][0]*dt*56.0/15.0+secondDerivatives2[4][0]*dt*32.0/9.0);
    dpsi3 = dpsi+(float) (secondDerivatives0[5][0]*dt*44.0/45.0-secondDerivatives1[5][0]*dt*56.0/15.0+secondDerivatives2[5][0]*dt*32.0/9.0);
    // k3 = secondDerivatives3
    secondDerivatives3 = evolveSecondDerivatives(theta+dtheta*dt*44.0/45.0-dtheta1*dt*56.0/15.0+dtheta2*dt*32.0/9.0, phi+dphi*dt*44.0/45.0-dphi1*dt*56.0/15.0+dphi2*dt*32.0/9.0, psi+dpsi*dt*44.0/45.0-dpsi1*dt*56.0/15.0+dpsi2*dt*32.0/9.0, R, alpha, m, mu, i1, i3, g, dtheta3, dphi3, dpsi3, dx3, dy3);
    N4 = (float) secondDerivatives2[0][0];
    dx4 = dx+(float) (secondDerivatives0[1][0]*dt*19372.0/6561.0-secondDerivatives1[1][0]*dt*25360.0/2187.0+secondDerivatives2[1][0]*dt*64448.0/6561.0-secondDerivatives3[1][0]*dt*212.0/729.0);
    dy4 = dy+(float) (secondDerivatives0[2][0]*dt*19372.0/6561.0-secondDerivatives1[2][0]*dt*25360.0/2187.0+secondDerivatives2[2][0]*dt*64448.0/6561.0-secondDerivatives3[2][0]*dt*212.0/729.0);
    dphi4 = dphi+(float) (secondDerivatives0[3][0]*dt*19372.0/6561.0-secondDerivatives1[3][0]*dt*25360.0/2187.0+secondDerivatives2[3][0]*dt*64448.0/6561.0-secondDerivatives3[3][0]*dt*212.0/729.0);
    dtheta4 = dtheta+(float) (secondDerivatives0[4][0]*dt*19372.0/6561.0-secondDerivatives1[4][0]*dt*25360.0/2187.0+secondDerivatives2[4][0]*dt*64448.0/6561.0-secondDerivatives3[4][0]*dt*212.0/729.0);
    dpsi4 = dpsi+(float) (secondDerivatives0[5][0]*dt*19372.0/6561.0-secondDerivatives1[5][0]*dt*25360.0/2187.0+secondDerivatives2[5][0]*dt*64448.0/6561.0-secondDerivatives3[5][0]*dt*212.0/729.0);
    // k3 = secondDerivatives3
    secondDerivatives4 = evolveSecondDerivatives(theta+dtheta*dt*19372.0/6561.0-dtheta1*dt*25360.0/2187.0+dtheta2*dt*64448.0/6561.0-dtheta3*dt*212.0/729.0, phi+dphi*dt*19372.0/6561.0-dphi1*dt*25360.0/2187.0+dphi2*dt*64448.0/6561.0-dphi3*dt*212.0/729.0, psi+dpsi*dt*19372.0/6561.0-dpsi1*dt*25360.0/2187.0+dpsi2*dt*64448.0/6561.0-dpsi3*dt*212.0/729.0, R, alpha, m, mu, i1, i3, g, dtheta4, dphi4, dpsi4, dx4, dy4);
    N5 = (float) secondDerivatives2[0][0];
    dx5 = dx+(float) (secondDerivatives0[1][0]*dt*9017.0/3168.0-secondDerivatives1[1][0]*dt*355.0/33.0+secondDerivatives2[1][0]*dt*46732.0/5247.0+secondDerivatives3[1][0]*dt*49.0/176.0-secondDerivatives4[1][0]*dt*5103.0/18656.0);
    dy5 = dy+(float) (secondDerivatives0[2][0]*dt*9017.0/3168.0-secondDerivatives1[2][0]*dt*355.0/33.0+secondDerivatives2[2][0]*dt*46732.0/5247.0+secondDerivatives3[2][0]*dt*49.0/176.0-secondDerivatives4[2][0]*dt*5103.0/18656.0);
    dphi5 = dphi+(float) (secondDerivatives0[3][0]*dt*9017.0/3168.0-secondDerivatives1[3][0]*dt*355.0/33.0+secondDerivatives2[3][0]*dt*46732.0/5247.0+secondDerivatives3[3][0]*dt*49.0/176.0-secondDerivatives4[3][0]*dt*5103.0/18656.0);
    dtheta5 = dtheta+(float) (secondDerivatives0[4][0]*dt*9017.0/3168.0-secondDerivatives1[4][0]*dt*355.0/33.0+secondDerivatives2[4][0]*dt*46732.0/5247.0+secondDerivatives3[4][0]*dt*49.0/176.0-secondDerivatives4[4][0]*dt*5103.0/18656.0);
    dpsi5 = dpsi+(float) (secondDerivatives0[5][0]*dt*9017.0/3168.0-secondDerivatives1[5][0]*dt*355.0/33.0+secondDerivatives2[5][0]*dt*46732.0/5247.0+secondDerivatives3[5][0]*dt*49.0/176.0-secondDerivatives4[5][0]*dt*5103.0/18656.0);
    // k3 = secondDerivatives3
    secondDerivatives5 = evolveSecondDerivatives(theta+dtheta*dt*9017.0/3168.0-dtheta1*dt*355.0/33.0+dtheta2*dt*46732.0/5247.0+dtheta3*dt*49.0/176.0-dtheta4*dt*5103.0/18656.0, phi+dphi*dt*9017.0/3168.0-dphi1*dt*355.0/33.0+dphi2*dt*46732.0/5247.0+dphi3*dt*49.0/176.0-dphi4*dt*5103.0/18656.0, psi+dpsi*dt*9017.0/3168.0-dpsi1*dt*355.0/33.0+dpsi2*dt*46732.0/5247.0+dpsi3*dt*49.0/176.0-dpsi4*dt*5103.0/18656.0, R, alpha, m, mu, i1, i3, g, dtheta5, dphi5, dpsi5, dx5, dy5);
    //N6 = (float) secondDerivatives2[0][0];
    //dx6 = dx+(float) secondDerivatives2[1][0]*dt;
    //dy6 = dy+(float) secondDerivatives2[2][0]*dt;
    //dphi6 = dphi+(float) secondDerivatives2[3][0]*dt;
    //dtheta6 = dtheta+(float) secondDerivatives2[4][0]*dt;
    //dpsi6 = dpsi+(float) secondDerivatives2[5][0]*dt;
    // k3 = secondDerivatives3
    //secondDerivatives6 = evolveSecondDerivatives(theta+dtheta*dt*35.0/384.0+dtheta2*dt*500.0/113.0+dtheta3*dt*125.0/192.0-dtheta4*dt*2187.0/6784.0+dtheta5*dt*11.0/84.0, phi+dphi*dt*35.0/384.0+dphi2*dt*500.0/113.0+dphi3*dt*125.0/192.0-dphi4*dt*2187.0/6784.0+dphi5*dt*11.0/84.0, psi+dpsi*dt*35.0/384.0+dpsi2*dt*500.0/113.0+dpsi3*dt*125.0/192.0-dpsi4*dt*2187.0/6784.0+dpsi5*dt*11.0/84.0, R, alpha, m, mu, i1, i3, g, dtheta6, dphi6, dpsi6, dx6, dy6);
    ds[0] = (35.0*N/384.0+500.0*N2/1113.0+125.0*N3/192.0-2187.0*N4/6784.0+11.0*N5/84.0);
    ds[1] = (35.0*dx/384.0+500.0*dx2/1113.0+125.0*dx3/192.0-2187.0*dx4/6784.0+11.0*dx5/84.0)*dt;
    ds[2] = (35.0*dy/384.0+500.0*dy2/1113.0+125.0*dy3/192.0-2187.0*dy4/6784.0+11.0*dy5/84.0)*dt;
    ds[3] = (35.0*dphi/384.0+500.0*dphi2/1113.0+125.0*dphi3/192.0-2187.0*dphi4/6784.0+11.0*dphi5/84.0)*dt;
    ds[4] = (35.0*dtheta/384.0+500.0*dtheta2/1113.0+125.0*dtheta3/192.0-2187.0*dtheta4/6784.0+11.0*dtheta5/84.0)*dt;
    ds[5] = (35.0*dpsi/384.0+500.0*dpsi2/1113.0+125.0*dpsi3/192.0-2187.0*dpsi4/6784.0+11.0*dpsi5/84.0)*dt;
    ds[6] = (float) (35.0*secondDerivatives0[1][0]/384.0+500.0*secondDerivatives2[1][0]/1113.0+125.0*secondDerivatives3[1][0]/192.0-2187.0*secondDerivatives4[1][0]/6784.0+11.0*secondDerivatives5[1][0]/84.0)*dt;
    ds[7] = (float) (35.0*secondDerivatives0[2][0]/384.0+500.0*secondDerivatives2[2][0]/1113.0+125.0*secondDerivatives3[2][0]/192.0-2187.0*secondDerivatives4[2][0]/6784.0+11.0*secondDerivatives5[2][0]/84.0)*dt;
    ds[8] = (float) (35.0*secondDerivatives0[3][0]/384.0+500.0*secondDerivatives2[3][0]/1113.0+125.0*secondDerivatives3[3][0]/192.0-2187.0*secondDerivatives4[3][0]/6784.0+11.0*secondDerivatives5[3][0]/84.0)*dt;
    ds[9] = (float) (35.0*secondDerivatives0[4][0]/384.0+500.0*secondDerivatives2[4][0]/1113.0+125.0*secondDerivatives3[4][0]/192.0-2187.0*secondDerivatives4[4][0]/6784.0+11.0*secondDerivatives5[4][0]/84.0)*dt;
    ds[10] = (float) (35.0*secondDerivatives0[5][0]/384.0+500.0*secondDerivatives2[5][0]/1113.0+125.0*secondDerivatives3[5][0]/192.0-2187.0*secondDerivatives4[5][0]/6784.0+11.0*secondDerivatives5[5][0]/84.0)*dt;
  }
  return ds;
}

void drawTop(float radius, float delta, float beta) {
  pushMatrix();
  rotateZ(PI);
  noFill();
  noStroke();
  float x, y, z, inrad;
  float hght = radius+radius*cos(beta), wdth = radius*sin(beta);
  
  for(float phi = 0.0; phi+delta/2.0 < PI-beta; phi += delta/2.0) {
    beginShape(QUAD_STRIP);
    texture(img2);
    textureMode(NORMAL);
    for(float theta = 0.0; theta+delta <= TWO_PI + delta; theta += delta) {
      x = radius * sin(phi) * cos(theta);
      z = radius * sin(phi) * sin(theta);
      y = -radius * cos(phi);
      
      vertex(x, y, z, theta/TWO_PI, (radius+y)/hght);
      
      x = radius * sin(phi + delta) * cos(theta);
      z = radius * sin(phi + delta) * sin(theta);
      y = -radius * cos(phi + delta);
      
      vertex(x, y, z, theta/TWO_PI, (radius+y)/hght);
    }
    endShape(CLOSE);
  }
  inrad = radius * sin(TWO_PI-beta);
  beginShape();
  texture(img2);
  textureMode(NORMAL);  
  for(float theta = 0.0; theta+delta < TWO_PI + delta; theta += delta) {
      x = inrad * cos(theta);
      z = inrad * sin(theta);
      vertex(x, hght-radius, z, (x+wdth)/(2*wdth), (z+wdth)/(2*wdth));
  }
  endShape(CLOSE);
  inrad = radius/10.0;
  y = sqrt(radius*radius*(99.0/100.0));
  beginShape(QUAD_STRIP);
  texture(img);
  textureMode(NORMAL);
  for(float theta = 0.0; theta+delta < TWO_PI + delta; theta += delta) {
      x = inrad * cos(theta);
      z = inrad * sin(theta);
      vertex(x, hght-radius, z, theta/TWO_PI, 0);
      vertex(x, y, z, (theta)/TWO_PI, 1);
  }  
  endShape(CLOSE);
  beginShape();
  texture(img);
  textureMode(NORMAL);  
  for(float theta = 0.0; theta+delta < TWO_PI + delta; theta += delta) {
      x = inrad * cos(theta);
      z = inrad * sin(theta);
      vertex(x, y, z, (x+wdth)/(2*wdth), (z+wdth)/(2*wdth));
  }
  endShape(CLOSE);
  popMatrix();
}

class Tippe {
  float x,y,z=0,theta,phi,psi,m,R,alpha,mu,i1,i3,rho,beta;
  float dx,dy,dphi,dtheta,dpsi,g=9.81, tdx, tdy;
  float ddx, ddy, ddtheta, ddphi, ddpsi, N;
  float sinTheta, cosTheta, sinPhi, cosPhi;
  float kt, kr, ug, energy, frictionPower, LA;
  float vABASE = 0, cMassZ;
  PVector vA, a, Lp, friction, torque, FNet;
  float[] RK4;
  Matrix Is, A, B, T, T1, DbigO, L, Omega, I;
  
  Tippe (float ix, float iy, float iz, float itheta, float iphi, float ipsi, float irho, float iR, float ibeta, float imu, float idx, float idy, float idphi, float idtheta, float idpsi) {
    x=ix;
    y=iy;
    z=iz;
    theta=itheta;
    phi=iphi;
    psi=ipsi;
    rho=irho;
    beta=ibeta;
    R=iR;
    mu=imu;
    dphi = idphi;
    dtheta = idtheta;
    dpsi = idpsi;
    dx = idx;
    dy = idy;
    alpha = (3.0-6*pow(cos(beta), 2)+3*pow(cos(beta), 4))/(8+12*cos(beta)-4*pow(cos(beta), 3));
    m=3.14*rho*R*R*R*(2.0/3.0+cos(beta)-cos(beta)*cos(beta)*cos(beta)/3.0);
    i1=-m*pow(alpha, 2)*pow(R, 2)+PI*rho*pow(R, 5)*(4.0/15.0+cos(beta)/4.0+pow(cos(beta), 3)/6.0-3*pow(cos(beta), 5)/20.0);
    i3=2*PI*rho*pow(R, 5)*(2.0/15.0+pow(cos(beta), 3)/3.0+cos(beta)*pow(sin(beta), 4)/4.0-pow(cos(beta), 5)/5.0);
    Is = new Matrix(new double[][] {{i1,0.,0.},{0.,i1,0.},{0.,0.,i3}});
    cMassZ = alpha*R;
  }
  void display() {
    pushMatrix();
    translate(x*1000, z*1000, -y*1000);
    rotateY(phi);
    rotateZ(theta);
    rotateY(psi);
    drawTop(R*1000, TWO_PI/60, beta);
    popMatrix();
  }
  void step() {
    RK4 = evolve(N, theta, phi, psi, R, alpha, m, mu, i1, i3, g, dtheta, dphi, dpsi, dx, dy);
    N = RK4[0];
    dx += RK4[6];
    dy += RK4[7];
    dphi += RK4[8];
    dtheta += RK4[9];
    ddtheta = RK4[9];
    dpsi += RK4[10];
    x += RK4[1];
    y += RK4[2];
    tdx = RK4[1];
    tdy = RK4[2];
    phi += RK4[3];
    theta += RK4[4];
    psi += RK4[5];
    sinTheta = sin(theta);
    cosTheta = cos(theta);
    sinPhi = sin(phi);
    cosPhi = cos(phi);
    kt = 0.5*m*(pow(dx-R*alpha*dtheta*cosPhi*cosTheta+R*alpha*dphi*sinPhi*sinTheta, 2) + pow(dy-R*alpha*dtheta*sinPhi*cosTheta-R*alpha*dphi*cosPhi*sinTheta, 2) +  pow(R*alpha*dtheta*sinTheta, 2));
    kr = 0.5*(i1*(dphi*dphi*sinTheta*sinTheta+dtheta*dtheta)+ i3*(dpsi+dphi*cosTheta)*(dpsi+dphi*cosTheta));
    ug =  R*alpha*m*g*cosTheta;
    energy = kt + kr - ug;
    vA = new PVector(dx-R*(dtheta*cosPhi+dpsi*sinPhi*sinTheta), dy-R*(dtheta*sinPhi-dpsi*cosPhi*sinTheta), 0);
    frictionPower = -mu*N*vA.mag();
    friction = vA.normalize().mult(-mu*N);
    A = new Matrix(new double[][] {{cosPhi, -sinPhi, 0}, {sinPhi, cosPhi, 0}, {0, 0, 1}});
    B = new Matrix(new double[][] {{cosTheta, 0, sinTheta}, {0, 1, 0}, {-sinTheta, 0, cosTheta}});
    T1 = A.times(B);
    I = (T1.times(Is)).times(T1.inverse());
    T1.set(0, 0, 0);
    T1.set(1, 0, 0);
    T1.set(2, 0, 1);
    DbigO = new Matrix(new double[][] {{dphi}, {dtheta}, {dpsi}});
    Omega = T1.times(DbigO);
    L = I.times(Omega);
    Lp = new PVector((float) L.get(0,0), (float) L.get(1,0), (float) L.get(2,0));
    a = new PVector(alpha*cosPhi*sinTheta, alpha*sinPhi*sinTheta, alpha*cosTheta-1).mult(R);
    LA = Lp.dot(a);
    torque = a.cross(new PVector(0,0,N).sub(vA.normalize().mult(mu*N)));
    FNet = new PVector(0,0,N-m*g).sub(vA.normalize().mult(mu*N));
    
    if (debug == true) {
      println("x");
      println(x);
      println("y");
      println(y);
      println("dx");
      println(dx);
      println("dy");
      println(dy);
      println("rho");
      println(rho);
      println("beta");
      println(beta);
      println("alpha");
      println(alpha);
      println("R");
      println(R);
      println("i1");
      println(i1);
      println("i3");
      println(i3);
      println("m");
      println(m);
      println("phi");
      println(phi);
      println("theta");
      println(theta);
      println("psi");
      println(psi);
      println("dtheta");
      println(dtheta);
    }
  }
}

void settings() {
  size(1600, 1000, P3D);
}

PVector rN, rG, rF, rAM, rAV, rM, rT, rFNet; //referenceVectors
float EScale, FScale;

void setup() {
  cam = new PeasyCam(this, 175);
  cam.rotateX(0.5);
  //cam.rotateY(0.5);
  cam.setMinimumDistance(50);
  cam.setMaximumDistance(500);
  tahoma = loadFont("Tahoma-20.vlw");
  //img = loadImage("wood.jpg");
  img = loadImage("wood.jpg");
  img2 = loadImage("redwood.jpg");
  img3 = loadImage("floor.jpg");
  //             ix iy iz   itheta iphi ipsi irho  iR  ibeta imu idx idy idphi idtheta idpsi
  top = new Tippe(0, 0, -0.015, 0.01, 0, 0, 150.0, 0.015, 1.75, 0.3, 0, 0, 0, 30., 135.0);
  frameRate(fps);
  top.step();
  EScale = -100/top.energy;
  FScale = -100/top.frictionPower;
  String[] args = {"Net Energy Graph"};
  EnergyGraph sa = new EnergyGraph();
  PApplet.runSketch(args, sa);
  String[] args2 = {"Friction Graph"};
  FrictionGraph sb = new FrictionGraph();
  PApplet.runSketch(args2, sb);
  String[] args3 = {"L·a Graph"};
  LDotAGraph sc = new LDotAGraph();
  PApplet.runSketch(args3, sc);
  String[] args4 = {"Translational Kinetic Energy Graph"};
  TranslationalEnergyGraph sd = new TranslationalEnergyGraph();
  PApplet.runSketch(args4, sd);
  String[] args5 = {"Rotational Kinetic Energy Graph"};
  RotationalEnergyGraph se = new RotationalEnergyGraph();
  PApplet.runSketch(args5, se);
  String[] args6 = {"Potential Energy Graph"};
  PotentialEnergyGraph sf = new PotentialEnergyGraph();
  PApplet.runSketch(args6, sf);
  //rN = new PVector(0,-top.N,0);
  rG = new PVector(0,top.m*top.g,0);
  //rF = new PVector(top.friction.x, top.friction.z, top.friction.y); // opposite vA
  rAM = new PVector((float) top.L.get(0,0), (float) top.L.get(2,0), (float) top.L.get(1,0));
  rAV = new PVector((float) top.Omega.get(0,0), (float) top.Omega.get(2,0), (float) top.Omega.get(1,0));
  //rM = new PVector(-top.dx*3, 0, -top.dy*3);
  rT = new PVector(top.torque.x, top.torque.z, top.torque.y);
  rFNet = new PVector(top.FNet.x, top.FNet.z, top.FNet.y);
  
}

int frameC = 0;
float drx, dry;

boolean isNaN(float x){return x != x;}

float sign(float x) {
  return x/abs(x);
}

void draw() {
  lights();
  if (debug == true && frameC < 20) {
    top.step();
    frameC += 1;
  } else if (debug == false) {
    for (int i = 0; i<stepsPerFrame; i++) {
      top.step();
    }
  }
  if (isNaN(top.x) == true || isNaN(top.y) == true) {
    println("approximation diverged");
    exit();
  } else { 
    background(102);
    noFill();
    noStroke();
    noTint();
    beginShape();
    texture(img3);
    textureMode(NORMAL);
    textureWrap(REPEAT);
    vertex(-1000, 0, -1000, 0, 0);
    vertex(-1000, 0, 1000, 0, 20);
    vertex(1000, 0, 1000, 20, 20);
    vertex(1000, 0, -1000, 20, 0);
    endShape();
    top.display();
    if (drawVectors == true) {
      //println(top.dphi+top.dpsi);
      drx = top.R*top.sinTheta*sin(top.psi)*1000;
      dry = top.R*top.sinTheta*cos(top.psi)*1000;
      // dr c of m = -(top.R-top.cMassZ*top.cosTheta)*1000;
      cam.beginHUD();
      textSize(25);
      fill(80,80,0);
      text("Friction", 60, 100);
      fill(80,0,0);
      text("Normal", 60, 140);
      fill(0,80,0);
      text("Gravity", 60, 180);
      fill(0,0,80);
      text("Angular Momentum", 60, 220);
      fill(80,0,80);
      text("Angular Velocity", 60, 260);
      fill(0,80,80);
      text("Linear Momentum", 60, 300);
      fill(20,20,20);
      text("Torque", 60, 340);
      fill(52,235,216);
      text("Net Force", 60, 380);
      cam.endHUD();
      drawVector(top.x*1000, 0, -top.y*1000, -top.friction.x, top.friction.z, -top.friction.y, TWO_PI/10, 80, 80, 0, rG); //friction
      drawVector(top.x*1000, 0, -top.y*1000, 0, top.N, 0, TWO_PI/10, 80, 0, 0, rG); //normal
      drawVector(top.x*1000, -(top.R-top.cMassZ*top.cosTheta)*1000, -top.y*1000, 0, -top.m*top.g, 0, TWO_PI/10, 0, 80, 0, rG); //g
      drawVector(top.x*1000, -(top.R-top.cMassZ*top.cosTheta)*1000, -top.y*1000, (float) top.Omega.get(0,0), (float) top.Omega.get(2,0), (float) top.Omega.get(1,0), TWO_PI/10, 80, 0, 80, rAV); // angular velocity
      drawVector(top.x*1000, -(top.R-top.cMassZ*top.cosTheta)*1000, -top.y*1000, -top.dx, 0, -top.dy, TWO_PI/10, 0, 80, 80, rG); //momentum
      drawVector(top.x*1000-vdx, -(top.R-top.cMassZ*top.cosTheta)*1000+vdy, -top.y*1000+vdz, top.FNet.x, top.FNet.z, top.FNet.y, TWO_PI/10, 52, 235, 216, rG); //FNet
      drawVector(top.x*1000, -(top.R-top.cMassZ*top.cosTheta)*1000, -top.y*1000, (float) top.L.get(0,0), (float) top.L.get(2,0), (float) top.L.get(1,0), TWO_PI/10, 0, 0, 80, rAM); // angular momentum
      drawVector(top.x*1000-vdx, -(top.R-top.cMassZ*top.cosTheta)*1000+vdy, -top.y*1000+vdz, top.torque.x, top.torque.z, top.torque.y, TWO_PI/10, 20, 20, 20, rT); //torque
    }
  //saveFrame("C:/Users/temp/Desktop/processing-3.5.3/video/f."+frameCount+".png");
  frameC += 1;
  }
}

// Graphs: Hacky asf but it works

public class EnergyGraph extends PApplet {
  
  float delta = 0.2;
  float[] yvals = new float[floor(1900/delta)];
  float initE = top.energy;
  int i = 0;
  float s = EScale;
  boolean saved = false;
  public void settings() {
    size(1900, 300);
    yvals[0] = top.energy;
    i = 1;
  }
  public void draw() {
    background(255);
    fill(0);
    stroke(0);
    strokeWeight(1);
    line(0, 150, 1900, 150);
    strokeWeight(1.2);
    textFont(tahoma);
    textAlign(CENTER);
    text("Net Energy Graph", 950, 30);
    stroke(255, 0, 0);
    if (i<yvals.length-1 && i <= frameC) {
      yvals[i] = top.energy;
      i += 1;
    }
    for (int j = 0; j < i-1; j++) {
      line(j*delta, (yvals[j])*s+150, (j+1)*delta, (yvals[j+1])*s+150);
    }
    
    if (i>=yvals.length-1 && saved == false) {
      save("energy.png");
      saved = true;
    }
  }
}

public class TranslationalEnergyGraph extends PApplet {
  
  float delta = 0.2;
  float[] yvals = new float[floor(1900/delta)];
  float initE = top.kt;
  int i = 0;
  float s = EScale;
  boolean saved = false;
  public void settings() {
    size(1900, 300);
    yvals[0] = top.kt;
    i = 1;
  }
  public void draw() {
    background(255);
    fill(0);
    stroke(0);
    strokeWeight(1);
    line(0, 150, 1900, 150);
    strokeWeight(1.2);
    textFont(tahoma);
    textAlign(CENTER);
    text("Translational Kinetic Energy Graph", 950, 30);
    stroke(255, 0, 0);
    if (i<yvals.length-1 && i <= frameC) {
      yvals[i] = top.kt;
      i += 1;
    }
    
    for (int j = 0; j < i-1; j++) {
      line(j*delta, (yvals[j])*s+150, (j+1)*delta, (yvals[j+1])*s+150);
    }
    
    if (i>=yvals.length-1 && saved == false) {
      save("tenergy.png");
      saved = true;
    }
  }
}

public class RotationalEnergyGraph extends PApplet {
  
  float delta = 0.2;
  float[] yvals = new float[floor(1900/delta)];
  float initE = top.kr;
  int i = 0;
  float s = EScale;
  boolean saved = false;
  public void settings() {
    size(1900, 300);
    yvals[0] = top.kr;
    i = 1;
  }
  public void draw() {
    background(255);
    fill(0);
    stroke(0);
    strokeWeight(1);
    line(0, 150, 1900, 150);
    strokeWeight(1.2);
    textFont(tahoma);
    textAlign(CENTER);
    text("Rotational Kinetic Energy Graph", 950, 30);
    stroke(255, 0, 0);
    if (i<yvals.length-1 && i <= frameC) {
      yvals[i] = top.kr;
      i += 1;
    }
    
    for (int j = 0; j < i-1; j++) {
      line(j*delta, (yvals[j])*s+150, (j+1)*delta, (yvals[j+1])*s+150);
    }
    
    if (i>=yvals.length-1 && saved == false) {
      save("renergy.png");
      saved = true;
    }
  }
}

public class PotentialEnergyGraph extends PApplet {
  
  float delta = 0.2;
  float[] yvals = new float[floor(1900/delta)];
  float initE = top.ug;
  int i = 0;
  float s = -EScale;
  boolean saved = false;
  public void settings() {
    size(1900, 300);
    yvals[0] = top.ug;
    i = 1;
  }
  public void draw() {
    background(255);
    fill(0);
    stroke(0);
    strokeWeight(1);
    line(0, 150, 1900, 150);
    strokeWeight(1.2);
    textFont(tahoma);
    textAlign(CENTER);
    text("Potential Energy Graph", 950, 30);
    stroke(255, 0, 0);
    if (i<yvals.length-1 && i <= frameC) {
      yvals[i] = top.ug;
      i += 1;
    }
    for (int j = 0; j < i-1; j++) {
      line(j*delta, (yvals[j])*s+150, (j+1)*delta, (yvals[j+1])*s+150);
    }
    
    if (i>=yvals.length-1 && saved == false) {
      save("penergy.png");
      saved = true;
    }
  }
}

public class FrictionGraph extends PApplet {
  
  float delta = 0.2;
  float[] yvals = new float[floor(1900/delta)];
  float initE = top.frictionPower;
  int i = 0;
  float s = -FScale;
  boolean saved = false;
  public void settings() {
    size(1900, 300);
    yvals[0] = top.frictionPower;
    i = 1;
  }
  public void draw() {
    background(255);
    fill(0);
    stroke(0);
    strokeWeight(1);
    line(0, 150, 1900, 150);
    strokeWeight(1.2);
    textFont(tahoma);
    textAlign(CENTER);
    text("Power of Friction Graph", 950, 30);
    stroke(255, 0, 0);
    if (i<yvals.length-1 && i <= frameC) {
      yvals[i] = top.frictionPower;
      i += 1;
    }
    
    for (int j = 0; j < i-1; j++) {
      line(j*delta, (yvals[j])*s+150, (j+1)*delta, (yvals[j+1])*s+150);
    }
    
    if (i>=yvals.length-1 && saved == false) {
      save("pfriction.png");
      saved = true;
    }
  }
}

public class LDotAGraph extends PApplet {
  
  float delta = 0.2;
  float[] yvals = new float[floor(1900/delta)];
  float initE = top.LA;
  int i = 0;
  float s = -100/initE;
  boolean saved = false;
  
  public void settings() {
    size(1900, 300);
    yvals[0] = top.LA;
    i = 1;
  }
  public void draw() {
    background(255);
    fill(0);
    stroke(0);
    strokeWeight(1);
    line(0, 150, 1900, 150);
    strokeWeight(1.2);
    textFont(tahoma);
    textAlign(CENTER);
    text("L·a Graph", 950, 30);
    stroke(255, 0, 0);
    if (i<yvals.length-1 && i <= frameC) {
      yvals[i] = top.LA;
      i += 1;
    }
    
    for (int j = 0; j < i-1; j++) {
      line(j*delta, (yvals[j])*s+150, (j+1)*delta, (yvals[j+1])*s+150);
    }
    
    if (i>=yvals.length-1 && saved == false) {
      save("ldota.png");
      saved = true;
    }
  }
}
