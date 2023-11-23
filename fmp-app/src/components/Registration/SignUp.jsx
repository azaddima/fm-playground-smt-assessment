import React from 'react';
import {
  MDBBtn,
  MDBContainer,
  MDBCard,
  MDBCardBody,
  MDBInput,
  MDBIcon,
  MDBRow,
  MDBCol,
  MDBCheckbox
}
  from 'mdb-react-ui-kit';

function App() {
  return (
    <MDBContainer className='my-5'>

      <MDBRow className='d-flex justify-content-center align-items-center'>
      <MDBCol col='12'>

        <MDBCard className='my-5 cascading-right' style={{ background: 'hsla(0, 0%, 100%, 0.55)', backdropFilter: 'blur(30px)', width: '50%' }}>
          <MDBCardBody className='p-5 shadow-5 text-center'>

            <h2 className="fw-bold mb-5">Sign up now</h2>

            <MDBInput wrapperClass='mb-4' label='Email' id='form23' type='email' />
            <MDBInput wrapperClass='mb-4' label='Password' id='form24' type='password' />

            <div className='d-flex justify-content-center mb-4'>
              <MDBCheckbox name='flexCheck' value='' id='flexCheckDefault' label='Subscribe to our newsletter' />
            </div>

            <MDBBtn className='w-100 mb-4' size='md'>sign up</MDBBtn>

            <div className="text-center">

              <p>or sign up with:</p>

              <MDBBtn tag='a' color='none' className='mx-3' style={{ color: '#1266f1' }}>
                <MDBIcon fab icon='facebook-f' size="sm" />
              </MDBBtn>

              <MDBBtn tag='a' color='none' className='mx-3' style={{ color: '#1266f1' }}>
                <MDBIcon fab icon='twitter' size="sm" />
              </MDBBtn>

              <MDBBtn tag='a' color='none' className='mx-3' style={{ color: '#1266f1' }}>
                <MDBIcon fab icon='google' size="sm" />
              </MDBBtn>

              <MDBBtn tag='a' color='none' className='mx-3' style={{ color: '#1266f1' }}>
                <MDBIcon fab icon='github' size="sm" />
              </MDBBtn>

            </div>

          </MDBCardBody>
        </MDBCard>
        </MDBCol>

      </MDBRow>
    </MDBContainer>
  );
}

export default App;