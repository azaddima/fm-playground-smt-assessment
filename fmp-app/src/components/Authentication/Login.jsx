import React from 'react';
import {
  MDBBtn,
  MDBContainer,
  MDBCard,
  MDBCardBody,
  MDBIcon,
}
  from 'mdb-react-ui-kit';

function Login() {

  function handleGoogleLogin() {
    window.open('http://localhost:8000/api/login', '_self')
  }
  return (
    <MDBContainer className='d-flex justify-content-center align-items-center' style={{ height: '100vh' }}>

      <MDBCard className='shadow-5' style={{ width: '30rem' }}>
        <MDBCardBody className='p-5 shadow-5 text-center'>

          <h2 className="mb-5">Login with your identity provider</h2>

          <MDBBtn style={{ backgroundColor: '#dd4b39' }} 
          onClick={handleGoogleLogin}
          >
            <MDBIcon className='me-2' fab icon='google' /> Login with Google
          </MDBBtn>
          <br />
          <br />
          <MDBBtn style={{ backgroundColor: '#000000' }} href='#'>
            <MDBIcon className='me-2' fab icon='github' /> Login with Github
          </MDBBtn>

        </MDBCardBody>
      </MDBCard>


    </MDBContainer>
  );
}

export default Login;